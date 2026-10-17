#lang racket/base
(require racket/match
         racket/list
         racket/file
         racket/path
         "cli-reader.rkt"
         "cli/schema.rkt"
         "cli/heaps.rkt"
         "cli/tables.rkt"
         "cli/metadata.rkt"
         "cli/header.rkt"
         "private/binary.rkt"
         "pe/imports.rkt"
         "pe/layout.rkt"
         "pe/relocs.rkt"
         "pe/write.rkt")
(provide assemble image-layout-report parse-il)

; ---------------------------------------------------------------------------
; layout constants (the PE layout itself lives in pe/)

(define image-bases (hasheq 'pe32 #x400000 'pe32+ #x140000000))
(define section-align #x2000)
(define file-align #x200)

; ---------------------------------------------------------------------------
; intermediate model

(struct ctx (asm-refs typerefs memberrefs))
(struct tdef (flags name ns extends methods))
(struct mdef (name flags sig body entry?))
(struct il-program (asm-refs typerefs memberrefs typedefs module-name entry-rid format))

; insertion-ordered interner: rids are 1-based and follow first-seen order
(struct interner (table [rows #:mutable]))
(define (make-interner) (interner (make-hash) '()))
(define (intern! it key)
  (define table (interner-table it))
  (or (hash-ref table key #f)
      (let ([rid (+ 1 (hash-count table))])
        (hash-set! table key rid)
        (set-interner-rows! it (cons key (interner-rows it)))
        rid)))
(define (interner-keys it) (reverse (interner-rows it)))

; ---------------------------------------------------------------------------
; flags and types

(define (typedef-flags kws)
  (for/fold ([acc 0]) ([k (in-list kws)])
    (bitwise-ior
     acc
     (case k
       [(public) #x1]
       ; auto is the layout keyword (0); autochar is the charset keyword
       [(private notpublic auto ansi class) 0]
       [(sequential) #x8]
       [(explicit) #x10]
       [(interface) #x20]
       [(abstract) #x80]
       [(sealed) #x100]
       [(specialname) #x400]
       [(unicode) #x10000]
       [(autochar) #x20000]
       [(beforefieldinit) #x100000]
       [else (error 'rangi "unsupported class flag ~a" k)]))))

(define access-flags
  '((public . #x6) (private . #x1) (family . #x4) (assembly . #x3)
    (famandassem . #x2) (famorassem . #x5)))
(define member-flags
  '((static . #x10) (final . #x20) (virtual . #x40) (hidebysig . #x80) (newslot . #x100)
    (abstract . #x400) (specialname . #x800) (rtspecialname . #x1000)))

(define (method-flags kws)
  (unless (memq 'static kws)
    (error 'rangi "only static methods are supported; missing static in ~s" kws))
  (define access
    (for/list ([k (in-list kws)] #:when (assq k access-flags))
      (cdr (assq k access-flags))))
  (when (> (length access) 1)
    (error 'rangi "more than one access modifier in ~s" kws))
  (for/fold ([acc (if (null? access) 0 (car access))])
            ([k (in-list kws)] #:unless (assq k access-flags))
    (bitwise-ior acc (cond [(assq k member-flags) => cdr]
                           [else (error 'rangi "unsupported method flag ~a" k)]))))

(define (type-code t)
  (case t
    [(void) #x01]
    [(int32) #x08]
    [(object) #x1C]
    [else (error 'rangi "unsupported type ~s" t)]))

(define (param-code t)
  (when (eq? t 'void) (error 'rangi "void is only valid as a return type"))
  (type-code t))

(define (method-sig ret params)
  (unless (list? params) (error 'rangi "malformed parameter list ~s" params))
  (bytes-append (bytes #x00)
                (compress-unsigned (length params))
                (bytes (type-code ret))
                (apply bytes-append (for/list ([t (in-list params)]) (bytes (param-code t))))))

; "System.Console" -> ("System" "Console"); a name without a dot has an empty namespace
(define (split-type-name sym)
  (define m (regexp-match #rx"^(.*)[.]([^.]*)$" (symbol->string sym)))
  (if m
      (values (cadr m) (caddr m))
      (values "" (symbol->string sym))))

(define (mscorlib-rid asm-refs)
  (or (hash-ref (interner-table asm-refs) "mscorlib" #f)
      (error 'rangi "System.Object requires an (.assembly extern mscorlib ...) reference")))

; ---------------------------------------------------------------------------
; pass A: model construction (no heap indexes yet)

(define (call-memberref! cx ret asm ty name params)
  (define asm-rid (hash-ref (interner-table (ctx-asm-refs cx)) (symbol->string asm) #f))
  (unless asm-rid (error 'rangi "unknown assembly reference ~a" asm))
  (define-values (ns short) (split-type-name ty))
  (define tr (intern! (ctx-typerefs cx) (list asm-rid ns short)))
  (intern! (ctx-memberrefs cx) (list tr (symbol->string name) (method-sig ret params))))

(define (encode-il cx il)
  (define entry? #f)
  (define maxstack 8)
  (define parts
    (for/list ([node (in-list il)])
      (match node
        [(list '.entrypoint) (set! entry? #t) #""]
        [(list '.maxstack n)
         (unless (and (exact-nonnegative-integer? n) (< n #x10000))
           (error 'rangi "invalid .maxstack ~s" n))
         (set! maxstack n)
         #""]
        [(list 'ret) (bytes #x2A)]
        [(list 'add) (bytes #x58)]
        [(list 'ldc.i n)
         (unless (and (exact-integer? n) (<= -2147483648 n 2147483647))
           (error 'rangi "ldc.i operand ~a is outside the int32 range" n))
         (bytes-append (bytes #x20) (integer->integer-bytes n 4 #t #f))]
        [(list 'call ret (list asm ty) name params)
         (define tok (call-memberref! cx ret asm ty name params))
         (bytes-append (bytes #x28) (le (bitwise-ior #x0A000000 tok) 4))]
        [other (error 'rangi "unsupported IL instruction ~s" other)])))
  (values (apply bytes-append parts) maxstack entry?))

; tiny headers imply maxstack 8 and no locals; anything else uses the fat header
(define (method-body code maxstack)
  (if (and (< (bytes-length code) 64) (<= maxstack 8))
      (bytes-append (bytes (bitwise-ior (arithmetic-shift (bytes-length code) 2) 2)) code)
      (bytes-append (le #x3003 2) (le maxstack 2) (le (bytes-length code) 4) (le 0 4) code)))

(define (encode-method cx class-name node)
  (match node
    [(list '.method prefix ret name params suffix il)
     (unless (and (list? suffix) (= (length suffix) 2) (memq 'cil suffix) (memq 'managed suffix))
       (error 'rangi "unsupported implementation flags ~s on ~a" suffix name))
     (define flags (method-flags prefix))
     (define sig (method-sig ret params))
     (define-values (code maxstack entry?) (encode-il cx il))
     (mdef (symbol->string name) flags sig (method-body code maxstack) entry?)]
    [_ (error 'rangi "malformed .method in ~a: ~s" class-name node)]))

(define (encode-methods cx class-name body)
  (define seen (make-hash))
  (for/list ([node (in-list body)])
    (define m (encode-method cx class-name node))
    (define key (list (mdef-name m) (mdef-sig m)))
    (when (hash-ref seen key #f)
      (error 'rangi "duplicate method ~a in ~a" (mdef-name m) class-name))
    (hash-set! seen key #t)
    m))

(define (class-named? sym)
  (lambda (c) (eq? (cadr c) sym)))

(define (parse-il program)
  (define asm-refs (make-interner))
  (define typerefs (make-interner))
  (define memberrefs (make-interner))
  (define cx (ctx asm-refs typerefs memberrefs))
  (define asm-def? #f)
  (define mod-name #f)
  (define fmt #f)
  (define classes
    (for/fold ([acc '()] #:result (reverse acc)) ([node (in-list program)])
      (match node
        [(list '.assembly 'extern filename _)
         (define name (read-assembly-meta (read-file filename)))
         (when (hash-ref (interner-table asm-refs) name #f)
           (error 'rangi "duplicate .assembly extern ~a" name))
         (intern! asm-refs name)
         acc]
        [(list '.assembly _ _)
         (when asm-def? (error 'rangi "only one .assembly directive is allowed"))
         (set! asm-def? #t)
         acc]
        [(list '.module name)
         (when mod-name (error 'rangi "only one .module directive is allowed"))
         (set! mod-name (symbol->string name))
         acc]
        [(list '.format f)
         (when fmt (error 'rangi "only one .format directive is allowed"))
         (unless (memq f '(pe32 pe32+)) (error 'rangi "unknown .format ~a, expected pe32 or pe32+" f))
         (set! fmt f)
         acc]
        [(list '.class flags name body)
         (cons (list flags name body) acc)]
        [_ (error 'rangi "unsupported top-level directive ~s" node)])))

  (when (check-duplicates (map cadr classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map cadr classes))))

  ; <Module> is always TypeDef row 1. Its methods move to a generated Program class,
  ; since the CLR rejects entry points declared on <Module>.
  (define module-cls
    (or (findf (class-named? '<Module>) classes) (list '() '<Module> '())))
  (define others (remove module-cls classes))
  (define moved? (pair? (caddr module-cls)))
  (when (and moved? (findf (class-named? 'Program) others))
    (error 'rangi "class Program clashes with the holder generated for <Module> methods"))
  (define ordered
    (append (list (if moved? (list (car module-cls) '<Module> '()) module-cls))
            (if moved? (list (list '() 'Program (caddr module-cls))) '())
            others))

  (define tdefs
    (for/list ([cls (in-list ordered)])
      (match-define (list flags name body) cls)
      (define-values (ns short) (split-type-name name))
      (define extends
        (cond
          [(or (eq? name '<Module>) (memq 'interface flags)) #f]
          [else (intern! typerefs (list (mscorlib-rid asm-refs) "System" "Object"))]))
      (define methods (encode-methods cx name body))
      (tdef (typedef-flags flags) short ns extends methods)))

  (define all-methods (append-map tdef-methods tdefs))
  (define entries
    (for/list ([m (in-list all-methods)] [rid (in-naturals 1)] #:when (mdef-entry? m))
      rid))
  (unless (= (length entries) 1)
    (error 'rangi "exactly one .entrypoint is required, found ~a" (length entries)))

  (il-program (interner-keys asm-refs)
              (interner-keys typerefs)
              (interner-keys memberrefs)
              tdefs
              mod-name
              (car entries)
              (or fmt 'pe32)))

; ---------------------------------------------------------------------------
; pass B: metadata tables

; starts-of: 1-based first rid of each owner's run of rows (MethodList, FieldList)
(define (starts-of counts)
  (let loop ([cs counts] [next 1] [acc '()])
    (if (null? cs)
        (reverse acc)
        (loop (cdr cs) (+ next (car cs)) (cons next acc)))))

; Adds the rows, sorts, and serialises the heaps and the #~ stream. The MVID is a
; zero placeholder in #GUID, filled at layout by the digest in metadata-chunk.
(define (build-metadata p asm-name mod-name)
  (define tb (make-tables))
  (define sh (make-strings-heap))
  (define bh (make-blob-heap))
  (define gh (make-guid-heap))
  (define uh (make-us-heap))
  (define (s x) (heap-add! sh x))
  (define (b x) (heap-add! bh x))
  (define tds (il-program-typedefs p))
  (define mdefs (append-map tdef-methods tds))
  (define starts (starts-of (map (λ (td) (length (tdef-methods td))) tds)))
  (define mvid (heap-add! gh (make-bytes 16 0)))
  (add-row! tb 'module 0 (s mod-name) mvid 0 0)
  (for ([r (in-list (il-program-typerefs p))])
    (match-let ([(list asm ns name) r])
      (add-row! tb 'typeref (coded-encode 'resolutionscope 'assemblyref asm) (s name) (s ns))))
  (for ([td (in-list tds)] [start (in-list starts)])
    (define ext (tdef-extends td))
    (add-row! tb 'typedef (tdef-flags td) (s (tdef-name td)) (s (tdef-ns td))
              (if ext (coded-encode 'typedeforref 'typeref ext) 0)
              1
              start))
  (for ([m (in-list mdefs)] [i (in-naturals)])
    (add-row! tb 'methoddef (rva-ref (method-sym i)) 0 (mdef-flags m) (s (mdef-name m))
              (b (mdef-sig m)) 1))
  (for ([r (in-list (il-program-memberrefs p))])
    (match-let ([(list tr name sig) r])
      (add-row! tb 'memberref (coded-encode 'memberrefparent 'typeref tr) (s name) (b sig))))
  (add-row! tb 'assembly 0 0 0 0 0 0 0 (s asm-name) 0)
  (for ([n (in-list (il-program-asm-refs p))])
    (add-row! tb 'assemblyref 0 0 0 0 0 0 (s n) 0 0))

  (sort-tables! tb)
  (define strs (pad-to (heap-serialise sh) 4))
  (define blobs (pad-to (heap-serialise bh) 4))
  (define-values (tilde table-fixups)
    (tables-stream tb
                   #:string-wide? (> (bytes-length strs) #xFFFF)
                   #:blob-wide? (> (bytes-length blobs) #xFFFF)
                   #:guid-wide? #f))
  (metadata-chunk (list (cons "#~" tilde)
                        (cons "#Strings" strs)
                        (cons "#US" (pad-to (heap-serialise uh) 4))
                        (cons "#GUID" (heap-serialise gh))
                        (cons "#Blob" blobs))
                  #:table-fixups table-fixups
                  #:mvid-index mvid))

; ---------------------------------------------------------------------------
; PE image

(define (method-sym i) (string->symbol (format "method:~a" i)))

(define (assemble p [out-path (make-temporary-file "rangi-~a.exe")])
  (write-pe-image (plan-image p (path->string (file-name-from-path out-path))) out-path
                  #:entry 'entry-stub
                  #:dirs pe-data-dirs)
  out-path)

; layout of the image that assemble writes for a file called file-name (V5 snapshots)
(define (image-layout-report p [file-name "image.exe"])
  (layout-report (plan-image p file-name)))

(define pe-data-dirs '((1 . import-dir) (5 . reloc) (12 . iat) (14 . cli-header)))

; places every chunk and returns the placed image, without writing a file
(define (plan-image p file-name)
  (define asm-name (regexp-replace #rx"[.][^.]*$" file-name ""))
  (define mod-name (or (il-program-module-name p) file-name))
  (define entry-rid (il-program-entry-rid p))
  (define fmt (il-program-format p))
  (define bodies
    (for*/list ([td (in-list (il-program-typedefs p))] [m (in-list (tdef-methods td))])
      (mdef-body m)))

  (define md (build-metadata p asm-name mod-name))
  (match-define (list iat import-dir lookup hint-name dll-name entry-stub)
    (mscoree-chunks fmt))
  (define cli-header
    (cli-header-chunk #:metadata-size (bytes-length (chunk-bytes md))
                      #:entry-rid entry-rid))
  (define body-chunks
    (for/list ([b (in-list bodies)] [i (in-naturals)])
      (chunk (method-sym i) 4 b '())))
  (define text
    (section ".text" #x60000020
             (append (list iat cli-header md) body-chunks
                     (list import-dir lookup hint-name dll-name entry-stub))))

  (define params
    (if (eq? fmt 'pe32+)
        (image-params 'pe32+ #x8664 #x22 3 #x8540 (hash-ref image-bases fmt) section-align file-align)
        (image-params 'pe32 #x14C #x102 3 #x8540 (hash-ref image-bases fmt) section-align file-align)))
  ; the relocation table holds the addresses of .text, so lay out .text before building it
  (define reloc
    (section ".reloc" #x42000040
             (list (base-relocation-chunk (layout-image params (list text))))))
  (layout-image params (list text reloc)))
