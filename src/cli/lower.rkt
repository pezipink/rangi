#lang racket/base
(require racket/match
         racket/list
         "../ilasm/syntax.rkt"
         "../private/binary.rkt")
(provide lower-module
         (struct-out cli-program)
         (struct-out tdef)
         (struct-out mdef))

; The CLI-level program: flags are bits, signatures and bodies are bytes, and
; references are rids. asm-refs, typerefs, and memberrefs are in row order.
(struct cli-program (asm-refs typerefs memberrefs typedefs module-name entry-rid format))
(struct tdef (flags name ns extends methods))
(struct mdef (name flags sig body entry?))

(struct ctx (asm-refs typerefs memberrefs))

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
; instructions and bodies

(define (call-memberref! cx ret asm ty name params)
  (define asm-rid (hash-ref (interner-table (ctx-asm-refs cx)) (symbol->string asm) #f))
  (unless asm-rid (error 'rangi "unknown assembly reference ~a" asm))
  (define-values (ns short) (split-type-name ty))
  (define tr (intern! (ctx-typerefs cx) (list asm-rid ns short)))
  (intern! (ctx-memberrefs cx) (list tr (symbol->string name) (method-sig ret params))))

(define (encode-il cx code)
  (apply bytes-append
         (for/list ([node (in-list code)])
           (match node
             [(list 'ret) (bytes #x2A)]
             [(list 'add) (bytes #x58)]
             [(list 'ldc.i n)
              (unless (and (exact-integer? n) (<= -2147483648 n 2147483647))
                (error 'rangi "ldc.i operand ~a is outside the int32 range" n))
              (bytes-append (bytes #x20) (integer->integer-bytes n 4 #t #f))]
             [(list 'call ret (list asm ty) name params)
              (define tok (call-memberref! cx ret asm ty name params))
              (bytes-append (bytes #x28) (le (bitwise-ior #x0A000000 tok) 4))]
             [other (error 'rangi "unsupported IL instruction ~s" other)]))))

; tiny headers imply maxstack 8 and no locals; anything else uses the fat header
(define (method-body code maxstack)
  (if (and (< (bytes-length code) 64) (<= maxstack 8))
      (bytes-append (bytes (bitwise-ior (arithmetic-shift (bytes-length code) 2) 2)) code)
      (bytes-append (le #x3003 2) (le maxstack 2) (le (bytes-length code) 4) (le 0 4) code)))

(define (encode-method cx m)
  (define flags (method-flags (method-decl-flags m)))
  (define sig (method-sig (method-decl-ret m) (method-decl-params m)))
  (define code (encode-il cx (method-decl-code m)))
  (mdef (symbol->string (method-decl-name m))
        flags
        sig
        (method-body code (method-decl-maxstack m))
        (method-decl-entry? m)))

(define (encode-methods cx class-name methods)
  (define seen (make-hash))
  (for/list ([m (in-list methods)])
    (define enc (encode-method cx m))
    (define key (list (mdef-name enc) (mdef-sig enc)))
    (when (hash-ref seen key #f)
      (error 'rangi "duplicate method ~a in ~a" (mdef-name enc) class-name))
    (hash-set! seen key #t)
    enc))

; ---------------------------------------------------------------------------
; model -> CLI program. Interning order matches the row order the writer emits.

(define (lower-module m)
  (define asm-refs (make-interner))
  (for ([n (in-list (module-model-asm-refs m))]) (intern! asm-refs n))
  (define typerefs (make-interner))
  (define memberrefs (make-interner))
  (define cx (ctx asm-refs typerefs memberrefs))
  (define tdefs
    (for/list ([cls (in-list (module-model-classes m))])
      (define name (class-decl-name cls))
      (define flags (class-decl-flags cls))
      (define-values (ns short) (split-type-name name))
      (define extends
        (cond
          [(or (eq? name '<Module>) (memq 'interface flags)) #f]
          [else (intern! typerefs (list (mscorlib-rid asm-refs) "System" "Object"))]))
      (define methods (encode-methods cx name (class-decl-methods cls)))
      (tdef (typedef-flags flags) short ns extends methods)))
  (define entry-rid
    (for/first ([md (in-list (append-map tdef-methods tdefs))]
                [rid (in-naturals 1)]
                #:when (mdef-entry? md))
      rid))
  (cli-program (interner-keys asm-refs)
               (interner-keys typerefs)
               (interner-keys memberrefs)
               tdefs
               (module-model-module-name m)
               entry-rid
               (module-model-format m)))
