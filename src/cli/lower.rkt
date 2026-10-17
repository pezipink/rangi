#lang racket/base
(require racket/match
         racket/list
         "../ilasm/syntax.rkt"
         "../private/binary.rkt"
         "heaps.rkt"
         (only-in "sigs.rkt" encode-localvar-sig encode-method-sig encode-method-instantiation
                  encode-typespec encode-type primitive-names)
         (only-in "../il/encode.rkt" find-opcode opcode-named)
         (only-in "../il/opcodes.rkt" opcode-operand)
         (only-in "../il/stack.rkt" compute-max-stack effect label-at
                  opcode-pop-count opcode-push-count opcode-flow-kind)
         (only-in "../il/labels.rkt" assemble-items assembly-code assembly-label-offset
                  label-symbol? label-name-of))
(provide lower-module
         (struct-out cli-program)
         (struct-out tdef)
         (struct-out mdef))

; The CLI-level program: flags are bits, signatures and bodies are bytes, and
; references are rids. asm-refs, typerefs, memberrefs, typespecs, methodspecs,
; genericparams, and standalone-sigs are in row order. us-heap holds the string literals
; used by ldstr. A memberref parent is a (cons 'typeref|'typespec rid); a methodspec method
; is (cons 'methoddef|'memberref rid); a genericparam owner is (cons 'methoddef rid).
(struct cli-program (asm-refs typerefs memberrefs typespecs methodspecs genericparams
                     typedefs module-name entry-rid format standalone-sigs us-heap))
(struct tdef (flags name ns extends methods))
(struct mdef (name flags sig body entry?))

; class-rids maps a module class name to its TypeDef rid. method-rids maps
; (list class name ret params), as written in the source, to (cons MethodDef-rid arity).
(struct ctx (asm-refs typerefs memberrefs typespecs methodspecs standalone-sigs us-heap
             class-rids method-rids))

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

; Source type to sigs.rkt descriptor, lowered in scope (cons class-arity method-arity).
; !N and !!N are class and method type variables (II.23.2.12), range-checked against the
; scope. A module class is (class (typedef . rid)). An external class is (class (typeref . rid)),
; and a generic instantiation is GENERICINST over that base (II.23.2.12).
(define (lower-type cx scope t)
  (cond
    [(memq t primitive-names) t]
    [(and (pair? t) (eq? (car t) 'szarray)) (list 'szarray (lower-type cx scope (cadr t)))]
    [(and (symbol? t) (tyvar-ref t))
     => (lambda (ref)
          (define mvar? (equal? (car ref) "!!"))
          (define limit (if mvar? (cdr scope) (car scope)))
          (unless (< (cdr ref) limit)
            (error 'rangi "type variable ~a out of range (~a declared)" t limit))
          (list (if mvar? 'mvar 'var) (cdr ref)))]
    [(and (pair? t) (memq (car t) '(class valuetype)))
     (define owner (cadr t))
     (define args (if (pair? (cddr t)) (caddr t) '()))
     (cond
       [(symbol? owner)
        (unless (null? args) (error 'rangi "generic class ~a is not lowered yet" owner))
        (list (car t) (cons 'typedef (module-class-rid cx owner)))]
       [else
        (define-values (asm ty) (asm-type-parts owner))
        (define tr (typeref-rid! cx asm ty (length args)))
        (if (null? args)
            (list (car t) (cons 'typeref tr))
            (list 'genericinst (list (car t) (cons 'typeref tr)) (lower-args cx scope args)))])]
    [else (error 'rangi "unsupported type ~s" t)]))

(define (lower-args cx scope args)
  (for/list ([a (in-list args)]) (lower-type cx scope a)))

; Primitive or array types, the subset that main's array lowering accepts as an element or
; a local.
(define (lowerable-type? t)
  (cond
    [(symbol? t) (and (memq t primitive-names) #t)]
    [(and (pair? t) (eq? (car t) 'szarray))
     (and (not (memq (cadr t) '(void typedref))) (lowerable-type? (cadr t)))]
    [else #f]))

(define (module-class-rid cx name)
  (or (hash-ref (ctx-class-rids cx) name #f)
      (error 'rangi "unknown class ~a" name)))

(define (asm-type-parts owner)
  (match owner
    [(list (? symbol? asm) (? symbol? ty)) (values asm ty)]
    [_ (error 'rangi "expected (assembly type) but got ~s" owner)]))

; MethodDefSig or MethodRefSig (II.23.2.1). arity is the number of method type parameters.
(define (method-sig cx scope ret params #:hasthis? [hasthis? #f] #:arity [arity 0])
  (unless (list? params) (error 'rangi "malformed parameter list ~s" params))
  (encode-method-sig (lower-type cx scope ret)
                     (lower-args cx scope params)
                     #:hasthis? hasthis? #:generic-arity arity))


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

; TypeRef row (II.22.38) for a type in an assembly reference. A generic type is named with
; its arity suffix (II.10.7), so List with two arguments is written with a grave accent and 2.
; Returns the rid.
(define (typeref-rid! cx asm ty arity)
  (define asm-rid (hash-ref (interner-table (ctx-asm-refs cx)) (symbol->string asm) #f))
  (unless asm-rid (error 'rangi "unknown assembly reference ~a" asm))
  (define-values (ns short) (split-type-name ty))
  (define name (if (zero? arity) short (format "~a`~a" short arity)))
  (intern! (ctx-typerefs cx) (list asm-rid ns name)))

; TypeSpec row (II.22.39): the blob is one Type. Returns the rid.
(define (typespec-rid! cx blob)
  (intern! (ctx-typespecs cx) blob))

; The parent of a MemberRef on an external owner: a TypeRef, or a TypeSpec when the owner
; is a generic instantiation (II.22.25, MemberRefParent).
(define (owner-parent! cx asm ty args scope)
  (cond
    [(null? args) (cons 'typeref (typeref-rid! cx asm ty 0))]
    [else
     (define tr (typeref-rid! cx asm ty (length args)))
     (define blob (encode-typespec
                   (list 'genericinst (list 'class (cons 'typeref tr))
                         (lower-args cx scope args))))
     (cons 'typespec (typespec-rid! cx blob))]))

; MemberRef row (II.22.25): parent, name, and signature blob. Returns the rid.
(define (member-ref! cx parent name sig)
  (intern! (ctx-memberrefs cx) (list parent (symbol->string name) sig)))

; MethodSpec row (II.22.29): method is (cons 'methoddef|'memberref rid), inst the
; instantiation blob (II.23.2.15). Returns the rid.
(define (methodspec-rid! cx method inst)
  (intern! (ctx-methodspecs cx) (list method (encode-method-instantiation inst))))

(define (token tag rid) (bitwise-ior tag rid))

; FieldSig (II.23.2.4): 0x06, then the field type
(define (field-token! cx asm ty name type)
  (when (eq? type 'void) (error 'rangi "void is not a valid field type"))
  (define parent (cons 'typeref (typeref-rid! cx asm ty 0)))
  (define sig (bytes-append (bytes #x06) (encode-type (lower-type cx '(0 . 0) type))))
  (token #x0A000000 (member-ref! cx parent name sig)))

(define (string-token cx s)
  (unless (string? s) (error 'rangi "ldstr operand must be a string, got ~s" s))
  (bitwise-ior #x70000000 (heap-add! (ctx-us-heap cx) s)))

; Operand kinds that take no token and no label resolution, so the opcode table
; encodes them as written. Token-carrying kinds are lowered by name below.
(define passable-operands
  '(InlineNone ShortInlineI InlineI InlineI8 ShortInlineR InlineR
    ShortInlineVar InlineVar ShortInlineBrTarget InlineBrTarget InlineSwitch))

(define token-instructions '(call callvirt newobj ldfld stfld ldstr newarr ldelem ldelema stelem))

; Element types for newarr, ldelem, ldelema, and stelem. A primitive name maps to its
; mscorlib System type explicitly. Void, typedref, and array element types are rejected.
(define primitive-element-types
  '((boolean . "System.Boolean") (char . "System.Char")
    (int8 . "System.SByte") (uint8 . "System.Byte")
    (int16 . "System.Int16") (uint16 . "System.UInt16")
    (int32 . "System.Int32") (uint32 . "System.UInt32")
    (int64 . "System.Int64") (uint64 . "System.UInt64")
    (float32 . "System.Single") (float64 . "System.Double")
    (intptr . "System.IntPtr") (uintptr . "System.UIntPtr")
    (object . "System.Object") (string . "System.String")))

(define (element-type-token! cx elem)
  (match elem
    [(? symbol?)
     (define entry (assq elem primitive-element-types))
     (unless entry (error 'rangi "array element type ~a is not supported" elem))
     (bitwise-ior #x01000000 (typeref-rid! cx 'mscorlib (string->symbol (cdr entry)) 0))]
    [(list (? symbol? asm) (? symbol? ty))
     #:when (not (memq asm '(szarray class valuetype)))
     (bitwise-ior #x01000000 (typeref-rid! cx asm ty 0))]
    [_ (error 'rangi "array element type ~s is not supported" elem)]))

; II.25.4.6: a catch handler starts with the exception object on the stack. finally and fault
; handlers start with an empty stack (III.1.7.5).
(define (handler-depth clause)
  (if (eq? (eh-clause-kind clause) 'catch) 1 0))

; endfault has the same encoding as endfinally, 0xDC (III.4.5, III.4.6), so the front end
; accepts both and lowering sees only endfinally.
(define (canonical-node node)
  (match node
    ['endfault 'endfinally]
    [(list 'endfault) 'endfinally]
    [_ node]))

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

(define (lower-instruction cx scope node nparams nlocals)
  (match node
    [(? symbol?)
     (unless (label-symbol? node) (check-passable node))
     node]
    [(list 'label (? symbol?)) node]
    [(list (or 'ldc.i 'ldc.i4) n) (ldc-i4-item n)]
    [(list (and base (or 'ldarg 'starg 'ldarga)) n) (var-item base n nparams "parameters")]
    [(list (and base (or 'ldloc 'stloc 'ldloca)) n) (var-item base n nlocals "locals")]
    [(list (or 'call 'callvirt) _ ...) (call-item cx scope node)]
    [(list 'newobj _ ...) (newobj-item cx scope node)]
    [(list (and op (or 'ldfld 'stfld)) (list asm ty) (? symbol? name) type)
     (list op (field-token! cx asm ty name type))]
    [(list 'ldstr s) (list 'ldstr (string-token cx s))]
    [(list (and op (or 'newarr 'ldelem 'ldelema 'stelem)) elem)
     (list op (element-type-token! cx elem))]
    [(list (? symbol? op) _ ...)
     (when (memq op token-instructions) (error 'rangi "malformed IL instruction ~s" node))
     (check-passable op)
     node]
    [_ (error 'rangi "unsupported IL item ~s" node)]))

; The owner of an external member: (asm ty), or (class (asm ty) (arg ...)) for a generic
; instantiation. Returns asm, ty, and the argument list (empty when not generic).
(define (external-owner owner node)
  (match owner
    [(list (? symbol? asm) (? symbol? ty)) (values asm ty '())]
    [(list 'class (list (? symbol? asm) (? symbol? ty)) (? list? args))
     (when (null? args) (error 'rangi "empty type argument list in ~s" node))
     (values asm ty args)]
    [_ (error 'rangi "unsupported call owner ~s in ~s" owner node)]))

; (inst T ...) after the parameters of a call names the type arguments of a generic method.
(define (inst-arg more node)
  (cond
    [(null? more) #f]
    [(and (null? (cdr more)) (pair? (car more)) (eq? (caar more) 'inst) (pair? (cdar more)))
     (cdar more)]
    [else (error 'rangi "malformed generic method arguments in ~s; expected (inst T ...)" node)]))

; call and callvirt. A symbol owner names a method in this module, with a MethodDef token
; (II.22.26). Any other owner is an external MemberRef (II.22.25). A generic method call
; names its instantiation with a MethodSpec (II.22.29).
(define (call-item cx scope node)
  (match node
    [(list (and op (or 'call 'callvirt)) ret owner (? symbol? name) params more ...)
     (define inst (inst-arg more node))
     (define callvirt? (eq? op 'callvirt))
     (cond
       [(and (pair? owner) (null? (cdr owner)) (symbol? (car owner)))
        (when callvirt?
          (error 'rangi "callvirt to same-module method ~a is not supported; only static methods are lowered" name))
        (define cls (car owner))
        (define hit (hash-ref (ctx-method-rids cx) (list cls name ret params) #f))
        (unless hit
          (error 'rangi "no method ~a in ~a with return ~a and parameters ~s" name cls ret params))
        (define rid (car hit))
        (define arity (cdr hit))
        (define ninst (if inst (length inst) 0))
        (unless (= ninst arity)
          (error 'rangi "~a.~a takes ~a type arguments, but the call gives ~a"
                 cls name arity ninst))
        (list op
              (if inst
                  (token #x2B000000
                         (methodspec-rid! cx (cons 'methoddef rid) (lower-args cx scope inst)))
                  (token #x06000000 rid)))]
       [else
        (define-values (asm ty args) (external-owner owner node))
        (define ninst (if inst (length inst) 0))
        (define parent (owner-parent! cx asm ty args scope))
        ; the callee's !N are the owner's type arguments and !!N its own, so they are
        ; lowered against (owner arity . method arity)
        (define sig (method-sig cx (cons (length args) ninst) ret params
                                #:hasthis? callvirt? #:arity ninst))
        (define mref (member-ref! cx parent name sig))
        (list op
              (if inst
                  (token #x2B000000
                         (methodspec-rid! cx (cons 'memberref mref) (lower-args cx scope inst)))
                  (token #x0A000000 mref)))])]
    [_ (error 'rangi "malformed IL instruction ~s" node)]))

(define (newobj-item cx scope node)
  (match node
    [(list 'newobj owner params)
     (define-values (asm ty args) (external-owner owner node))
     (define parent (owner-parent! cx asm ty args scope))
     (define sig (method-sig cx (cons (length args) 0) 'void params #:hasthis? #t))
     (list 'newobj (token #x0A000000 (member-ref! cx parent '.ctor sig)))]
    [_ (error 'rangi "malformed IL instruction ~s" node)]))

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

; Lowers the instruction list to labels.rkt items and assembles them. Returns the assembly
; (code bytes and label offsets) and the maximum stack depth computed from the control-flow
; graph. Each catch handler starts with one item, the exception object (III.1.7.5, II.25.4.6).
(define (encode-il cx scope code0 nparams nlocals ret-void? handlers)
  (define code (map canonical-node code0))
  (define items
    (for/list ([node (in-list code)]) (lower-instruction cx scope node nparams nlocals)))
  (define effects
    (for/list ([node (in-list code)] [item (in-list items)])
      (node-effect node item ret-void?)))
  (values (assemble-items items)
          (compute-max-stack effects
                             #:handlers (for/list ([h (in-list handlers)])
                                          (cons (eh-clause-handler-start h) (handler-depth h))))))

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

; III.1.7.5: a tiny header is possible only without locals, exception clauses, code under
; 64 bytes, and maxstack 8 or less. Otherwise the fat header is used, with LocalVarSigTok
; and the InitLocals flag (0x10). MoreSects (0x08) announces the EH section after the code.
(define (method-body code maxstack locals-tok init? eh)
  (cond
    [(and (not eh) (zero? locals-tok) (< (bytes-length code) 64) (<= maxstack 8))
     (bytes-append (bytes (bitwise-ior (arithmetic-shift (bytes-length code) 2) 2)) code)]
    [else
     (define flags (bitwise-ior #x3003 (if init? #x10 0) (if eh #x08 0)))
     ; II.25.4.5: the EH section starts on a 4-byte boundary; the fat header is 12 bytes
     (define pad (if eh (modulo (- 4 (modulo (bytes-length code) 4)) 4) 0))
     (bytes-append (le flags 2)
                   (le maxstack 2)
                   (le (bytes-length code) 4)
                   (le locals-tok 4)
                   code
                   (make-bytes pad 0)
                   (or eh #""))]))

; II.25.4.6 Flags: catch 0x0000, finally 0x0002, fault 0x0004. ClassToken is the exception
; type for a catch and 0 otherwise.
(define (clause-flags c)
  (case (eh-clause-kind c)
    [(catch) #x0000]
    [(finally) #x0002]
    [(fault) #x0004]))

(define (clause-class-token cx c)
  (define class (eh-clause-class c))
  (if class
      (bitwise-ior #x01000000 (typeref-rid! cx (car class) (cadr class) 0))
      0))

; II.25.4.5, II.25.4.6: one fat EHTable section (Kind 0x01 | FatFormat 0x40, 3-byte DataSize)
; with a 24-byte clause per handler. Offsets come from the assembled labels.
(define (eh-section cx asm clauses)
  (define (at l) (assembly-label-offset asm l))
  (define clause-bytes
    (for/list ([c (in-list clauses)])
      (define ts (at (eh-clause-try-start c)))
      (define hs (at (eh-clause-handler-start c)))
      (bytes-append (le (clause-flags c) 4)
                    (le ts 4)
                    (le (- (at (eh-clause-try-end c)) ts) 4)
                    (le hs 4)
                    (le (- (at (eh-clause-handler-end c)) hs) 4)
                    (le (clause-class-token cx c) 4))))
  (define body (apply bytes-append clause-bytes))
  (bytes-append (bytes #x41) (le (+ 4 (bytes-length body)) 3) body))

; Returns the MethodDef row and its GenericParam rows (number, name, owner). Method type
; parameters are !!N in this method's scope (II.23.2.12); the class has no type parameters yet.
(define (encode-method cx class-name rid m)
  (define name (method-decl-name m))
  (define gparams (method-decl-gparams m))
  (define nmth (length gparams))
  (for ([g (in-list gparams)])
    (unless (and (null? (generic-param-specials g)) (null? (generic-param-constraints g)))
      (error 'rangi "constraints on generic parameters of ~a.~a are not lowered yet"
             class-name name)))
  (when (and (pair? gparams) (method-decl-entry? m))
    (error 'rangi "the entry point ~a.~a cannot be generic" class-name name))
  (define scope (cons 0 nmth))
  (define flags (method-flags (method-decl-flags m)))
  (define params (method-decl-params m))
  (define ld (method-decl-locals m))
  (define local-types (if ld (map local-var-type (locals-decl-vars ld)) '()))
  (define init? (and ld (locals-decl-init? ld)))
  (define clauses (method-decl-handlers m))
  (for ([t (in-list local-types)])
    (when (eq? t 'void) (error 'rangi "local of type void in ~a.~a" class-name name)))
  (define sig (method-sig cx scope (method-decl-ret m) params #:arity nmth))
  (define-values (asm computed)
    (encode-il cx scope (method-decl-code m) (length params) (length local-types)
               (eq? (method-decl-ret m) 'void) clauses))
  (define code (assembly-code asm))
  (define maxstack (effective-maxstack (method-decl-maxstack m) computed))
  ; StandAloneSig table tag 0x11, II.22.36
  (define locals-tok
    (if (null? local-types)
        0
        (bitwise-ior #x11000000
                     (intern! (ctx-standalone-sigs cx)
                              (encode-localvar-sig
                               (for/list ([t (in-list local-types)])
                                 (lower-type cx scope t)))))))
  (values
   (mdef (symbol->string name)
         flags
         sig
         (method-body code maxstack locals-tok init?
                      (and (pair? clauses) (eh-section cx asm clauses)))
         (method-decl-entry? m))
   (for/list ([g (in-list gparams)] [i (in-naturals)])
     (list i (symbol->string (generic-param-name g)) (cons 'methoddef rid)))))

; first-rid is the MethodDef rid of the first method of this class.
(define (encode-methods cx class-name first-rid methods)
  (define seen (make-hash))
  (for/fold ([mdefs '()] [gps '()] #:result (values (reverse mdefs) (append* (reverse gps))))
            ([m (in-list methods)] [rid (in-naturals first-rid)])
    (define-values (enc rows) (encode-method cx class-name rid m))
    (define key (list (mdef-name enc) (mdef-sig enc)))
    (when (hash-ref seen key #f)
      (error 'rangi "duplicate method ~a in ~a" (mdef-name enc) class-name))
    (hash-set! seen key #t)
    (values (cons enc mdefs) (cons rows gps))))

; ---------------------------------------------------------------------------
; model -> CLI program. Interning order matches the row order the writer emits.

(define (lower-module m)
  (define classes (module-model-classes m))
  (for ([cls (in-list classes)] #:unless (null? (class-decl-gparams cls)))
    (error 'rangi "generic class ~a is not lowered yet" (class-decl-name cls)))
  (define asm-refs (make-interner))
  (for ([n (in-list (module-model-asm-refs m))]) (intern! asm-refs n))
  (define typerefs (make-interner))
  (define memberrefs (make-interner))
  (define typespecs (make-interner))
  (define methodspecs (make-interner))
  (define standalone-sigs (make-interner))
  (define us-heap (make-us-heap))
  (define class-rids (make-hash))
  (for ([cls (in-list classes)] [rid (in-naturals 1)])
    (hash-set! class-rids (class-decl-name cls) rid))
  (define method-rids (make-hash))
  (for/fold ([next 1]) ([cls (in-list classes)])
    (for/fold ([next next]) ([md (in-list (class-decl-methods cls))])
      (define key (list (class-decl-name cls) (method-decl-name md)
                        (method-decl-ret md) (method-decl-params md)))
      (when (hash-ref method-rids key #f)
        (error 'rangi "duplicate method ~a in ~a" (method-decl-name md) (class-decl-name cls)))
      (hash-set! method-rids key (cons next (length (method-decl-gparams md))))
      (add1 next)))
  (define cx (ctx asm-refs typerefs memberrefs typespecs methodspecs standalone-sigs us-heap
                  class-rids method-rids))
  (define-values (tdefs gps)
    (for/fold ([tdefs '()] [gps '()] [next-rid 1]
               #:result (values (reverse tdefs) (append* (reverse gps))))
              ([cls (in-list classes)])
      (define name (class-decl-name cls))
      (define flags (class-decl-flags cls))
      (define-values (ns short) (split-type-name name))
      (define extends
        (cond
          [(or (eq? name '<Module>) (memq 'interface flags)) #f]
          [else (intern! typerefs (list (mscorlib-rid asm-refs) "System" "Object"))]))
      (define-values (mdefs rows) (encode-methods cx name next-rid (class-decl-methods cls)))
      (values (cons (tdef (typedef-flags flags) short ns extends mdefs) tdefs)
              (cons rows gps)
              (+ next-rid (length mdefs)))))
  (define entry-rid
    (for/first ([md (in-list (append-map tdef-methods tdefs))]
                [rid (in-naturals 1)]
                #:when (mdef-entry? md))
      rid))
  (cli-program (interner-keys asm-refs)
               (interner-keys typerefs)
               (interner-keys memberrefs)
               (interner-keys typespecs)
               (interner-keys methodspecs)
               gps
               tdefs
               (module-model-module-name m)
               entry-rid
               (module-model-format m)
               (interner-keys standalone-sigs)
               us-heap))

