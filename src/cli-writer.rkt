#lang racket/base
(require racket/match
         racket/list
         racket/file
         racket/path
         "cli-reader.rkt"
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
; heaps

(struct heap (port table))
(define (make-heap seed)
  (define port (open-output-bytes))
  (write-bytes seed port)
  (heap port (make-hash)))
(define (heap-size h) (file-position (heap-port h)))
(define (heap-bytes h) (get-output-bytes (heap-port h)))

(define (string-index! h s)
  (cond
    [(equal? s "") 0]
    [(hash-ref (heap-table h) s #f) => values]
    [else
     (define off (heap-size h))
     (write-bytes (string->bytes/utf-8 s) (heap-port h))
     (write-byte 0 (heap-port h))
     (hash-set! (heap-table h) s off)
     off]))

(define (blob-index! h b)
  (cond
    [(hash-ref (heap-table h) b #f) => values]
    [else
     (define off (heap-size h))
     (write-bytes (compress-unsigned (bytes-length b)) (heap-port h))
     (write-bytes b (heap-port h))
     (hash-set! (heap-table h) b off)
     off]))

; ---------------------------------------------------------------------------
; pass B: metadata tables

(struct tbl (id kinds rows))

(define (starts-of counts)
  (let loop ([cs counts] [next 1] [acc '()])
    (if (null? cs)
        (reverse acc)
        (loop (cdr cs) (+ next (car cs)) (cons next acc)))))

(define (build-tables p sh bh mod-name asm-name)
  (define (s x) (string-index! sh x))
  (define (b x) (blob-index! bh x))
  (define tds (il-program-typedefs p))
  (define mdefs (append-map tdef-methods tds))
  (define starts (starts-of (map (λ (td) (length (tdef-methods td))) tds)))
  (define module-t
    (tbl #x00 '(u2 str guid guid guid)
         (list (list 0 (s mod-name) 1 0 0))))
  (define typeref-t
    (tbl #x01 '((coded 2 (0 #x23 1)) str str)
         (for/list ([r (in-list (il-program-typerefs p))])
           (match-let ([(list asm ns name) r])
             (list (bitwise-ior (arithmetic-shift asm 2) 2) (s name) (s ns))))))
  (define typedef-t
    (tbl #x02 '(u4 str str (coded 2 (2 1)) (simple 4) (simple 6))
         (for/list ([td (in-list tds)] [start (in-list starts)])
           (define ext (tdef-extends td))
           (list (tdef-flags td) (s (tdef-name td)) (s (tdef-ns td))
                 (if ext (bitwise-ior (arithmetic-shift ext 2) 1) 0)
                 1
                 start))))
  (define methoddef-t
    (tbl #x06 '(u4 u2 u2 str blob (simple 8))
         (for/list ([m (in-list mdefs)] [i (in-naturals)])
           (list (rva-ref (method-sym i)) 0 (mdef-flags m) (s (mdef-name m)) (b (mdef-sig m)) 1))))
  (define memberref-t
    (tbl #x0A '((coded 3 (2 1 #x1A 6 #x1B)) str blob)
         (for/list ([r (in-list (il-program-memberrefs p))])
           (match-let ([(list tr name sig) r])
             (list (bitwise-ior (arithmetic-shift tr 3) 1) (s name) (b sig))))))
  (define assembly-t
    (tbl #x20 '(u4 u2 u2 u2 u2 u4 blob str str)
         (list (list 0 0 0 0 0 0 0 (s asm-name) 0))))
  (define assemblyref-t
    (tbl #x23 '(u2 u2 u2 u2 u4 blob str str blob)
         (for/list ([n (in-list (il-program-asm-refs p))])
           (list 0 0 0 0 0 0 (s n) 0 0))))
  (list module-t typeref-t typedef-t methoddef-t memberref-t assembly-t assemblyref-t))

; returns the metadata root and its fixups. Each MethodDef RVA is a 4-byte field whose
; value is the body chunk's RVA, so it is left zero here and patched at layout. The MVID
; is a digest over the other streams, so it is also left zero and filled at layout.
(define (metadata-bytes p asm-name mod-name)
  (define sh (make-heap #"\0"))
  (define bh (make-heap #"\0"))
  (define tables
    (filter (λ (t) (pair? (tbl-rows t))) (build-tables p sh bh mod-name asm-name)))
  (define strs (pad-to (heap-bytes sh) 4))
  (define blobs (pad-to (heap-bytes bh) 4))
  (define us (bytes 0 0 0 0))
  (define counts
    (for/hash ([t (in-list tables)]) (values (tbl-id t) (length (tbl-rows t)))))
  (define strbig (> (bytes-length strs) #xFFFF))
  (define blobbig (> (bytes-length blobs) #xFFFF))
  (define (kind-width k)
    (match k
      ['u2 2]
      ['u4 4]
      ['str (if strbig 4 2)]
      ['blob (if blobbig 4 2)]
      ['guid 2]
      [(list 'simple t) (if (> (hash-ref counts t 0) #xFFFF) 4 2)]
      [(list 'coded bits targets)
       (define mx (for/fold ([m 0]) ([t (in-list targets)]) (max m (hash-ref counts t 0))))
       (if (< mx (expt 2 (- 16 bits))) 2 4)]))
  (define cells
    (for*/list ([t (in-list tables)]
                [row (in-list (tbl-rows t))]
                [(v w) (in-parallel row (map kind-width (tbl-kinds t)))])
      (cons v w)))
  (define table-bytes
    (apply bytes-append
           (for/list ([c (in-list cells)])
             (le (if (rva-ref? (car c)) 0 (car c)) (cdr c)))))
  ; byte offset of each RVA field within the table stream, after its 24-byte header and row counts
  (define rva-cells
    (let loop ([cs cells] [pos 0] [acc '()])
      (cond
        [(null? cs) (reverse acc)]
        [else
         (define c (car cs))
         (loop (cdr cs) (+ pos (cdr c))
               (if (rva-ref? (car c)) (cons (cons pos (rva-ref-target (car c))) acc) acc))])))
  (define heap-flags (+ (if strbig 1 0) (if blobbig 4 0)))
  (define valid (for/sum ([t (in-list tables)]) (arithmetic-shift 1 (tbl-id t))))
  (define tilde
    (pad-to (bytes-append (le 0 4) (bytes 2 0 heap-flags 1) (le valid 8) (le 0 8)
                          (apply bytes-append
                                 (for/list ([t (in-list tables)])
                                   (le (length (tbl-rows t)) 4)))
                          table-bytes)
            4))
  (define streams
    (list (cons "#~" tilde)
          (cons "#Strings" strs)
          (cons "#US" us)
          (cons "#GUID" (make-bytes 16 0))
          (cons "#Blob" blobs)))
  (define (stream-header name off size)
    (bytes-append (le off 4) (le size 4)
                  (pad-to (bytes-append (string->bytes/utf-8 name) #"\0") 4)))
  (define header-len
    (for/sum ([st (in-list streams)]) (bytes-length (stream-header (car st) 0 0))))
  (define offsets
    (let loop ([ss streams] [off (+ #x20 header-len)] [acc '()])
      (if (null? ss)
          (reverse acc)
          (loop (cdr ss) (+ off (bytes-length (cdr (car ss)))) (cons off acc)))))
  (define headers
    (apply bytes-append
           (for/list ([st (in-list streams)] [off (in-list offsets)])
             (stream-header (car st) off (bytes-length (cdr st))))))
  (define root
    (bytes-append #"BSJB" (le 1 2) (le 1 2) (le 0 4)
                  (le 12 4) (pad-to #"v4.0.30319\0" 4)
                  (le 0 2) (le (length streams) 2)))
  (define table-start (+ 24 (* 4 (length tables))))
  ; the MVID is a digest of every stream except #GUID, with the RVA fields filled in
  (define guid-offset
    (for/first ([st (in-list streams)] [off (in-list offsets)] #:when (equal? (car st) "#GUID"))
      off))
  (define digest-spans
    (for/list ([st (in-list streams)] [off (in-list offsets)] #:unless (equal? (car st) "#GUID"))
      (cons off (+ off (bytes-length (cdr st))))))
  (values (bytes-append root headers (apply bytes-append (map cdr streams)))
          (append
           (for/list ([rc (in-list rva-cells)])
             (fixup (+ (car offsets) table-start (car rc)) 'rva32 (cdr rc)))
           (list (digest guid-offset digest-spans)))))

; ---------------------------------------------------------------------------
; PE image

(define (method-sym i) (string->symbol (format "method:~a" i)))

; a 4-byte metadata cell holding the RVA of target; metadata-bytes emits it as a fixup
(struct rva-ref (target))

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

  (define-values (md-bytes md-fixups) (metadata-bytes p asm-name mod-name))
  (match-define (list iat import-dir lookup hint-name dll-name entry-stub)
    (mscoree-chunks fmt))
  (define cli-header
    (chunk 'cli-header 4
           (bytes-append (le #x48 4) (le 2 2) (le 0 2)
                         (make-bytes 4 0) (le (bytes-length md-bytes) 4)
                         (le 1 4)
                         (le (bitwise-ior #x06000000 entry-rid) 4)
                         (make-bytes 48 0))
           (list (fixup 8 'rva32 'metadata))))
  (define metadata (chunk 'metadata 4 md-bytes md-fixups))
  (define body-chunks
    (for/list ([b (in-list bodies)] [i (in-naturals)])
      (chunk (method-sym i) 4 b '())))
  (define text
    (section ".text" #x60000020
             (append (list iat cli-header metadata) body-chunks
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
