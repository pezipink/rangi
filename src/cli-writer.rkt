#lang racket/base
(require racket/match
         racket/list
         racket/file
         racket/path
         "cli-reader.rkt")
(provide assemble parse-il)

; ---------------------------------------------------------------------------
; byte helpers

(define (le n k)
  (unless (and (exact-nonnegative-integer? n) (< n (expt 2 (* 8 k))))
    (error 'rangi "value ~a does not fit in ~a bytes" n k))
  (define b (make-bytes k 0))
  (for ([i (in-range k)])
    (bytes-set! b i (bitwise-and (arithmetic-shift n (* -8 i)) #xFF)))
  b)

(define (align n a) (* a (quotient (+ n a -1) a)))

(define (pad-to bs n)
  (bytes-append bs (make-bytes (- (align (bytes-length bs) n) (bytes-length bs)) 0)))

(define (compressed n)
  (cond
    [(< n #x80) (bytes n)]
    [(< n #x4000) (bytes (bitwise-ior #x80 (arithmetic-shift n -8)) (bitwise-and n #xFF))]
    [(< n #x20000000)
     (bytes (bitwise-ior #xC0 (arithmetic-shift n -24))
            (bitwise-and (arithmetic-shift n -16) #xFF)
            (bitwise-and (arithmetic-shift n -8) #xFF)
            (bitwise-and n #xFF))]
    [else (error 'rangi "blob of ~a bytes is too large" n)]))

(define (text-va off) (+ text-rva off))

; ---------------------------------------------------------------------------
; layout constants

(define image-base #x400000)
(define section-align #x2000)
(define file-align #x200)
(define headers-size #x200)
(define text-rva #x2000)
(define md-off #x50)
(define cli-off #x08)
(define hint-name-bytes (bytes-append (le 0 2) #"_CorExeMain\0"))
(define dll-name-bytes #"mscoree.dll\0")

; DOS stub with the standard 0x80 e_lfanew and the "This program cannot be run" message.
(define dos-header
  (let ([b (make-bytes #x84 0)])
    (bytes-copy! b 0 (bytes #x4D #x5A #x90 #x00 #x03 #x00 #x00 #x00 #x04 #x00 #x00 #x00
                            #xFF #xFF #x00 #x00 #xB8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x40))
    (bytes-copy! b #x3C (le #x80 4))
    (bytes-copy! b #x40 (bytes #x0E #x1F #xBA #x0E #x00 #xB4 #x09 #xCD #x21 #xB8 #x01 #x4C #xCD #x21))
    (bytes-copy! b #x4E (string->bytes/utf-8 "This program cannot be run in DOS mode.\r\r\n$"))
    (bytes-copy! b #x80 (bytes #x50 #x45 #x00 #x00))
    b))

; ---------------------------------------------------------------------------
; intermediate model

(struct ctx (asm-refs typerefs memberrefs))
(struct tdef (flags name ns extends methods))
(struct mdef (name flags sig body entry?))
(struct il-program (asm-refs typerefs memberrefs typedefs module-name entry-rid))

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
                (compressed (length params))
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
              (car entries)))

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
     (write-bytes (compressed (bytes-length b)) (heap-port h))
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

(define (build-tables p sh bh mod-name asm-name rva-of)
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
           (list (rva-of i) 0 (mdef-flags m) (s (mdef-name m)) (b (mdef-sig m)) 1))))
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

; returns the complete metadata root; rva-of maps a 0-based method index to its body RVA
(define (metadata-bytes p asm-name mod-name rva-of)
  (define sh (make-heap #"\0"))
  (define bh (make-heap #"\0"))
  (define tables
    (filter (λ (t) (pair? (tbl-rows t))) (build-tables p sh bh mod-name asm-name rva-of)))
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
  (define table-bytes
    (apply bytes-append
           (for/list ([t (in-list tables)])
             (define widths (map kind-width (tbl-kinds t)))
             (apply bytes-append
                    (for*/list ([row (in-list (tbl-rows t))]
                                [(v w) (in-parallel row widths)])
                      (le v w))))))
  (define heap-flags (+ (if strbig 1 0) (if blobbig 4 0)))
  (define valid (for/sum ([t (in-list tables)]) (arithmetic-shift 1 (tbl-id t))))
  (define tilde
    (pad-to (bytes-append (le 0 4) (bytes 2 0 heap-flags 1) (le valid 8) (le 0 8)
                          (apply bytes-append
                                 (for/list ([t (in-list tables)])
                                   (le (length (tbl-rows t)) 4)))
                          table-bytes)
            4))
  (define mvid (subbytes (sha256-bytes (bytes-append tilde strs us blobs)) 0 16))
  (define streams
    (list (cons "#~" tilde)
          (cons "#Strings" strs)
          (cons "#US" us)
          (cons "#GUID" mvid)
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
  (bytes-append root headers (apply bytes-append (map cdr streams))))

; ---------------------------------------------------------------------------
; PE image

(define (section-header name vsize va rawsize rawptr chars)
  (bytes-append (pad-to (string->bytes/utf-8 name) 8)
                (le vsize 4) (le va 4) (le rawsize 4) (le rawptr 4)
                (le 0 4) (le 0 4) (le 0 2) (le 0 2) (le chars 4)))

(define (assemble p [out-path (make-temporary-file "rangi-~a.exe")])
  (define file-name (path->string (file-name-from-path out-path)))
  (define asm-name (regexp-replace #rx"[.][^.]*$" file-name ""))
  (define mod-name (or (il-program-module-name p) file-name))
  (define entry-rid (il-program-entry-rid p))
  (define bodies
    (for*/list ([td (in-list (il-program-typedefs p))] [m (in-list (tdef-methods td))])
      (mdef-body m)))

  ; metadata size does not depend on the RVA values, so measure once with zeros
  (define md-len (bytes-length (metadata-bytes p asm-name mod-name (λ (i) 0))))

  (define il-start (+ md-off (align md-len 4)))
  (define-values (il-offs il-end)
    (for/fold ([offs '()] [pos il-start]) ([b (in-list bodies)])
      (define at (align pos 4))
      (values (cons at offs) (+ at (bytes-length b)))))
  (define il-vec (list->vector (reverse il-offs)))
  (define (rva-of i) (text-va (vector-ref il-vec i)))

  (define import-off (align il-end 4))
  (define lookup-off (+ import-off #x28))
  (define hn-off (+ lookup-off 8))
  (define dll-off (+ hn-off (bytes-length hint-name-bytes)))
  (define stub-off (align (+ dll-off (bytes-length dll-name-bytes)) 4))
  (define text-size (+ stub-off 6))
  (define text-raw (align text-size file-align))
  (define reloc-rva (+ text-rva (align text-size section-align)))
  (define size-of-image (+ reloc-rva (align 12 section-align)))

  (define md (metadata-bytes p asm-name mod-name rva-of))
  (unless (= (bytes-length md) md-len)
    (error 'rangi "internal error: metadata size changed between passes"))

  (define text (make-bytes text-size 0))
  (define (put! off bs) (bytes-copy! text off bs))
  (put! 0 (bytes-append (le (text-va hn-off) 4) (le 0 4)))
  (put! cli-off (bytes-append (le #x48 4) (le 2 2) (le 0 2)
                              (le (text-va md-off) 4) (le md-len 4)
                              (le 1 4)
                              (le (bitwise-ior #x06000000 entry-rid) 4)
                              (make-bytes 48 0)))
  (put! md-off md)
  (for ([b (in-list bodies)] [i (in-naturals)])
    (put! (vector-ref il-vec i) b))
  (put! import-off (bytes-append (le (text-va lookup-off) 4) (le 0 4) (le 0 4)
                                 (le (text-va dll-off) 4) (le text-rva 4)
                                 (make-bytes 20 0)))
  (put! lookup-off (bytes-append (le (text-va hn-off) 4) (le 0 4)))
  (put! hn-off hint-name-bytes)
  (put! dll-off dll-name-bytes)
  ; the entry stub jumps through the IAT slot using its absolute address
  (put! stub-off (bytes-append (bytes #xFF #x25) (le (+ image-base text-rva) 4)))

  ; one HIGHLOW relocation for the operand of the stub's jump
  (define reloc-target (+ (text-va stub-off) 2))
  (define reloc-block
    (bytes-append (le (bitwise-and reloc-target (bitwise-not #xFFF)) 4)
                  (le 12 4)
                  (le (bitwise-ior (arithmetic-shift 3 12) (bitwise-and reloc-target #xFFF)) 2)
                  (le 0 2)))

  (define coff-header
    (bytes-append (le #x14C 2) (le 2 2) (le 0 4) (le 0 4) (le 0 4) (le #xE0 2) (le #x102 2)))
  (define dirs
    (hash 1 (cons (text-va import-off) #x28)
          5 (cons reloc-rva 12)
          12 (cons text-rva 8)
          14 (cons (text-va cli-off) #x48)))
  (define dir-bytes
    (apply bytes-append
           (for/list ([i (in-range 16)])
             (let ([d (hash-ref dirs i (cons 0 0))])
               (bytes-append (le (car d) 4) (le (cdr d) 4))))))
  (define opt-header
    (bytes-append
     (le #x10B 2) (bytes 6 5)
     (le text-raw 4) (le headers-size 4) (le 0 4)
     (le (text-va stub-off) 4) (le text-rva 4) (le reloc-rva 4)
     (le image-base 4) (le section-align 4) (le file-align 4)
     (le 4 2) (le 0 2) (le 0 2) (le 0 2) (le 4 2) (le 0 2) (le 0 4)
     (le size-of-image 4) (le headers-size 4) (le 0 4)
     (le 3 2) (le #x8540 2)
     (le #x100000 4) (le #x1000 4) (le #x100000 4) (le #x1000 4)
     (le 0 4) (le 16 4)
     dir-bytes))
  (define section-headers
    (bytes-append
     (section-header ".text" text-size text-rva text-raw headers-size #x60000020)
     (section-header ".reloc" 12 reloc-rva headers-size (+ headers-size text-raw) #x42000040)))
  (define pe-header
    (bytes-append dos-header coff-header opt-header section-headers))

  (define file-bytes
    (bytes-append (pad-to pe-header headers-size)
                  (pad-to text file-align)
                  (pad-to reloc-block file-align)))
  (call-with-output-file out-path
    (λ (out) (write-bytes file-bytes out))
    #:exists 'truncate/replace)
  out-path)
