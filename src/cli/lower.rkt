#lang racket/base
(require racket/match
         racket/list
         "../ilasm/syntax.rkt"
         "../private/binary.rkt"
         "heaps.rkt"
         (only-in "../il/encode.rkt" find-opcode opcode-named)
         (only-in "../il/opcodes.rkt" opcode-operand)
         (only-in "../il/stack.rkt" compute-max-stack effect label-at
                  opcode-pop-count opcode-push-count opcode-flow-kind)
         (only-in "../il/labels.rkt" assemble-items assembly-code label-symbol? label-name-of))
(provide lower-module
         (struct-out cli-program)
         (struct-out tdef)
         (struct-out mdef))

; The CLI-level program: flags are bits, signatures and bodies are bytes, and
; references are rids. asm-refs, typerefs, memberrefs, and standalone-sigs are in
; row order. us-heap holds the string literals used by ldstr.
(struct cli-program (asm-refs typerefs memberrefs typedefs module-name entry-rid format
                     standalone-sigs us-heap))
(struct tdef (flags name ns extends methods))
(struct mdef (name flags sig body entry?))

(struct ctx (asm-refs typerefs memberrefs standalone-sigs us-heap))

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

(define (value-type-code t what)
  (when (eq? t 'void) (error 'rangi "void is not a valid ~a type" what))
  (type-code t))

; MethodDefSig/MethodRefSig (II.23.2.1). HASTHIS (0x20) marks instance calls.
(define (method-sig ret params #:cc [cc #x00])
  (unless (list? params) (error 'rangi "malformed parameter list ~s" params))
  (bytes-append (bytes cc)
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

; MemberRef row (II.22.25): parent type, name, and signature blob. Returns the rid.
(define (member-ref! cx asm ty name sig)
  (define asm-rid (hash-ref (interner-table (ctx-asm-refs cx)) (symbol->string asm) #f))
  (unless asm-rid (error 'rangi "unknown assembly reference ~a" asm))
  (define-values (ns short) (split-type-name ty))
  (define tr (intern! (ctx-typerefs cx) (list asm-rid ns short)))
  (intern! (ctx-memberrefs cx) (list tr (symbol->string name) sig)))

(define (method-token! cx cc ret asm ty name params)
  (bitwise-ior #x0A000000
               (member-ref! cx asm ty name (method-sig ret params #:cc cc))))

; FieldSig (II.23.2.4): 0x06, then the field type
(define (field-token! cx asm ty name type)
  (bitwise-ior #x0A000000
               (member-ref! cx asm ty name (bytes-append (bytes #x06) (bytes (value-type-code type "field"))))))

(define (string-token cx s)
  (unless (string? s) (error 'rangi "ldstr operand must be a string, got ~s" s))
  (bitwise-ior #x70000000 (heap-add! (ctx-us-heap cx) s)))

; LocalVarSig (II.23.2.6): 0x07, compressed count, then one type per local.
; Placeholder for the encoder in the other lane; lives here only until the lanes merge.
(define (encode-localvar-sig types)
  (apply bytes-append (bytes #x07) (compress-unsigned (length types))
         (for/list ([t (in-list types)]) (bytes (value-type-code t "local")))))

; Operand kinds that take no token and no label resolution, so the opcode table
; encodes them as written. Token-carrying kinds are lowered by name below.
(define passable-operands
  '(InlineNone ShortInlineI InlineI InlineI8 ShortInlineR InlineR
    ShortInlineVar InlineVar ShortInlineBrTarget InlineBrTarget InlineSwitch))

(define token-instructions '(call callvirt newobj ldfld stfld ldstr))

(define (check-passable name)
  (define op (find-opcode name))
  (cond
    [(not op) (error 'rangi "unknown IL instruction ~a" name)]
    [(not (memq (opcode-operand op) passable-operands))
     (error 'rangi "unsupported IL instruction ~a" name)]))

; ldc.i4 uses the shortest form, III.3.40 (ldc.i4.m1, ldc.i4.0 to .8, ldc.i4.s, ldc.i4)
(define (ldc-i4-item n)
  (unless (and (exact-integer? n) (<= -2147483648 n 2147483647))
    (error 'rangi "ldc.i4 operand ~a is outside the int32 range" n))
  (cond
    [(eqv? n -1) 'ldc.i4.m1]
    [(<= 0 n 8) (string->symbol (format "ldc.i4.~a" n))]
    [(<= -128 n 127) (list 'ldc.i4.s n)]
    [else (list 'ldc.i4 n)]))

; ldarg/ldloc/stloc have 0-3 macros; all have the .s form (index <= 255), then the long form
(define (var-item base n count what)
  (unless (and (exact-integer? n) (<= 0 n) (< n count))
    (error 'rangi "~a index ~a is out of range: the method has ~a ~a" base n count what))
  (define name (symbol->string base))
  (cond
    [(and (memq base '(ldarg ldloc stloc)) (<= n 3))
     (string->symbol (format "~a.~a" name n))]
    [(<= n 255) (list (string->symbol (string-append name ".s")) n)]
    [else (list base n)]))

(define (lower-instruction cx node nparams nlocals)
  (match node
    [(? symbol?)
     (unless (label-symbol? node) (check-passable node))
     node]
    [(list 'label (? symbol?)) node]
    [(list (or 'ldc.i 'ldc.i4) n) (ldc-i4-item n)]
    [(list (and base (or 'ldarg 'starg 'ldarga)) n) (var-item base n nparams "parameters")]
    [(list (and base (or 'ldloc 'stloc 'ldloca)) n) (var-item base n nlocals "locals")]
    [(list (and op (or 'call 'callvirt)) ret (list asm ty) (? symbol? name) params)
     (list op (method-token! cx (if (eq? op 'call) #x00 #x20) ret asm ty name params))]
    [(list 'newobj (list asm ty) params)
     (list 'newobj (method-token! cx #x20 'void asm ty '.ctor params))]
    [(list (and op (or 'ldfld 'stfld)) (list asm ty) (? symbol? name) type)
     (list op (field-token! cx asm ty name type))]
    [(list 'ldstr s) (list 'ldstr (string-token cx s))]
    [(list (? symbol? op) _ ...)
     (when (memq op token-instructions) (error 'rangi "malformed IL instruction ~s" node))
     (check-passable op)
     node]
    [_ (error 'rangi "unsupported IL item ~s" node)]))

; Stack effect of one source node, for the depth analysis in il/stack.rkt. Call-like
; instructions take their pop and push counts from the signature, because the table has Varpop.
(define (node-effect node item ret-void?)
  (cond
    [(and (symbol? node) (label-symbol? node)) (label-at (label-name-of node))]
    [(and (pair? node) (eq? (car node) 'label)) (label-at (cadr node))]
    [(or (eq? node 'ret) (and (pair? node) (eq? (car node) 'ret)))
     (effect 'ret (if ret-void? 0 1) 0 'return '())]
    [(and (pair? node) (memq (car node) '(call callvirt)))
     (effect (car node)
             (+ (length (list-ref node 4)) (if (eq? (car node) 'callvirt) 1 0))
             (if (eq? (cadr node) 'void) 0 1)
             'next '())]
    [(and (pair? node) (eq? (car node) 'newobj))
     (effect 'newobj (length (caddr node)) 1 'next '())]
    [else
     (define name (if (symbol? item) item (car item)))
     (define op (opcode-named name))
     (define flow (opcode-flow-kind op))
     (define targets
       (cond
         [(not (memq flow '(branch cond leave))) '()]
         [(eq? name 'switch) (cdr item)]
         [else (list (cadr item))]))
     (effect name (opcode-pop-count op) (opcode-push-count op) flow targets)]))

; Lowers the instruction list to labels.rkt items and assembles them. Returns the code
; bytes and the maximum stack depth computed from the control-flow graph.
(define (encode-il cx code nparams nlocals ret-void?)
  (define items
    (for/list ([node (in-list code)]) (lower-instruction cx node nparams nlocals)))
  (define effects
    (for/list ([node (in-list code)] [item (in-list items)])
      (node-effect node item ret-void?)))
  (values (assembly-code (assemble-items items))
          (compute-max-stack effects)))

; .maxstack given: it is an explicit override and must be at least the computed depth.
; Otherwise the default of 8 is kept unless the code needs more.
(define (effective-maxstack explicit computed)
  (cond
    [explicit
     (when (< explicit computed)
       (error 'rangi ".maxstack ~a is smaller than the computed maximum stack depth ~a"
              explicit computed))
     explicit]
    [else (max 8 computed)]))

; III.1.7.5: a tiny header is possible only without locals, code under 64 bytes,
; and maxstack 8 or less. Otherwise the fat header is used, with LocalVarSigTok
; and the InitLocals flag (0x10).
(define (method-body code maxstack locals-tok init?)
  (cond
    [(and (zero? locals-tok) (< (bytes-length code) 64) (<= maxstack 8))
     (bytes-append (bytes (bitwise-ior (arithmetic-shift (bytes-length code) 2) 2)) code)]
    [else
     (bytes-append (le (bitwise-ior #x3003 (if init? #x10 0)) 2)
                   (le maxstack 2)
                   (le (bytes-length code) 4)
                   (le locals-tok 4)
                   code)]))

(define (encode-method cx m)
  (define flags (method-flags (method-decl-flags m)))
  (define params (method-decl-params m))
  (define locals (method-decl-locals m))
  (define sig (method-sig (method-decl-ret m) params))
  (define-values (code computed)
    (encode-il cx (method-decl-code m) (length params) (length locals)
               (eq? (method-decl-ret m) 'void)))
  (define maxstack (effective-maxstack (method-decl-maxstack m) computed))
  ; StandAloneSig table tag 0x11, II.22.36
  (define locals-tok
    (if (null? locals)
        0
        (bitwise-ior #x11000000 (intern! (ctx-standalone-sigs cx) (encode-localvar-sig locals)))))
  (mdef (symbol->string (method-decl-name m))
        flags
        sig
        (method-body code maxstack locals-tok
                     (and (method-decl-init? m) (pair? locals)))
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
  (define standalone-sigs (make-interner))
  (define us-heap (make-us-heap))
  (define cx (ctx asm-refs typerefs memberrefs standalone-sigs us-heap))
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
               (module-model-format m)
               (interner-keys standalone-sigs)
               us-heap))
