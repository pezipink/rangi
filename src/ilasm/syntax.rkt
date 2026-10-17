#lang racket/base
(require racket/match
         racket/list
         racket/file
         "../cli-reader.rkt"
         (only-in "../cli/sigs.rkt" primitive-names))
(provide parse-il
         tyvar-ref
         (struct-out module-model)
         (struct-out asm-ref)
         (struct-out class-decl)
         (struct-out override-decl)
         (struct-out field-decl)
         (struct-out data-decl)
         (struct-out method-decl)
         (struct-out generic-param)
         (struct-out locals-decl)
         (struct-out local-var)
         (struct-out eh-clause))

; The front end's output. It holds names and instructions as written, with no tokens,
; heap indexes, or flag bits. cli/lower.rkt resolves those.
; subsystem is 'console (the default) or 'windows (.subsystem). platform is 'anycpu (the default),
; 'x86, or '32bitpreferred (.platform). Both are names here; lower and image map them to flags.
; data is the list of data-decl blocks (.data, II.16) in source order.
(struct module-model (asm-refs classes module-name format dll? subsystem platform data))
; An .assembly extern (II.22.5 AssemblyRef). name comes from the referenced file. version is four
; 16-bit parts, and token is the 8-byte public key token or #"" when none is given.
(struct asm-ref (name version token) #:transparent)
; extends is the base type as written: a bare symbol for a class in this module, (asm ty) for an
; external class, or #f for the default System.Object (II.22.37).
; name is the full name: Outer/Inner for a nested class (II.10.3). enclosing is the full name of
; the enclosing class, or #f for a top-level class. overrides is a list of override-decl, in source order.
; implements is a list of interface names in source order, each as in extends (II.22.23).
(struct class-decl (flags name gparams extends methods fields enclosing overrides implements))
; A .override directive (II.22.27 MethodImpl): owner is the base class as in extends, name, ret and
; params are the base method's signature. The body is the method of the same name and signature in
; the class that declares the override.
(struct override-decl (owner name ret params) #:transparent)
; A field (II.22.15). flags are FieldAttributes keywords; type is a type form (II.22.15).
; init is #f, or (prim . value) for a literal field: an integral primitive and its integer value.
; at is #f, or the name of a data-decl whose bytes are the field's initial value (FieldRVA, II.22.18).
(struct field-decl (flags type name init at) #:transparent)
; A data block (II.16): name is the symbol a field's `at` refers to, bytes its initial value.
(struct data-decl (name bytes) #:transparent)
; handlers: list of eh-clause in source order. maxstack is #f when there is no .maxstack.
(struct method-decl (flags ret name gparams params code maxstack entry? locals handlers))
; exception clause (II.25.4.6): kind is catch, finally, fault or filter. class is (asm ty) for a
; catch, the filter block's label name for a filter, and #f otherwise; the four labels are names
; without the colon.
; try is [try-start, try-end), handler is [handler-start, handler-end).
(struct eh-clause (kind class try-start try-end handler-start handler-end))
; A generic parameter (II.22.20). specials are class, valuetype or .ctor.
; constraints are type forms (II.22.21).
(struct generic-param (name specials constraints) #:transparent)
; .locals init (...) sets init? to #t. vars is a list of local-var.
(struct locals-decl (init? vars) #:transparent)
(struct local-var (type name) #:transparent)

(define (class-named? sym)
  (lambda (c) (eq? (cadr c) sym)))

; Type variables are !N for class parameters and !!N for method parameters (II.23.2.12).
; Returns (cons "!" N) or (cons "!!" N), or #f for anything else.
(define (tyvar-ref sym)
  (define m (regexp-match #rx"^(!!?)([0-9]+)$" (symbol->string sym)))
  (and m (cons (cadr m) (string->number (caddr m)))))

; Type forms: a primitive name, a type variable, or (class Name) / (valuetype Name) with
; optional type arguments as a list, which must not be empty. Name is a bare symbol for a
; type in this module, or (asm ty) for a type in a referenced assembly. ncls and nmth are
; the number of class and method parameters in scope.
(define (check-type who t ncls nmth)
  (match t
    [(? symbol?)
     (cond
       [(memq t primitive-names) (void)]
       [(tyvar-ref t)
        => (lambda (ref)
             (define limit (if (equal? (car ref) "!!") nmth ncls))
             (unless (< (cdr ref) limit)
               (error 'rangi "~a: type variable ~a out of range (~a declared)" who t limit)))]
       [else (error 'rangi "~a: unknown type ~s" who t)])]
    [(list (or 'class 'valuetype) (or (? symbol?) (list (? symbol?) (? symbol?)))) (void)]
    [(list (or 'class 'valuetype) (or (? symbol?) (list (? symbol?) (? symbol?))) '())
     (error 'rangi "~a: empty generic argument list in ~s" who t)]
    [(list (or 'class 'valuetype) (or (? symbol?) (list (? symbol?) (? symbol?))) (? list? args))
     (for ([a (in-list args)]) (check-type who a ncls nmth))]
    ; SZARRAY (II.23.2.12): the element type follows the ARRAY marker
    [(list 'szarray elem)
     (when (memq elem '(void typedref))
       (error 'rangi "~a: array element type cannot be ~a" who elem))
     (check-type who elem ncls nmth)]
    ; ARRAY (II.23.2.13) with zero lower bounds and no sizes: (array ELEM RANK)
    [(list 'array elem (? exact-positive-integer? rank))
     (when (memq elem '(void typedref))
       (error 'rangi "~a: array element type cannot be ~a" who elem))
     (check-type who elem ncls nmth)]
    [(cons 'array _)
     (error 'rangi "~a: array type must be (array ELEM RANK) with a positive rank, got ~s (bounded arrays are not supported)" who t)]
    [_ (error 'rangi "~a: malformed type ~s" who t)]))

(define gp-special-keywords '(class valuetype .ctor))

; NAME, or (NAME special ... constraint ...). Specials and constraints may be mixed.
(define (parse-generic-param who node ncls nmth)
  (define-values (name rest)
    (match node
      [(? symbol? n) (values n '())]
      [(cons (? symbol? n) r) (values n r)]
      [_ (error 'rangi "~a: malformed generic parameter ~s" who node)]))
  (define-values (specials constraints)
    (for/fold ([sp '()] [cs '()] #:result (values (reverse sp) (reverse cs)))
              ([x (in-list rest)])
      (cond
        [(memq x gp-special-keywords) (values (cons x sp) cs)]
        [(pair? x) (check-type who x ncls nmth) (values sp (cons x cs))]
        [(and (symbol? x) (tyvar-ref x)) (check-type who x ncls nmth) (values sp (cons x cs))]
        [else (error 'rangi "~a: invalid constraint ~s on ~a" who x name)])))
  (when (check-duplicates specials)
    (error 'rangi "~a: duplicate special constraint on ~a" who name))
  (generic-param name specials constraints))

(define (typarams-count tp) (if tp (length (cdr tp)) 0))

; tp is the whole (.typarams GP ...) list, or #f when there are no generic parameters.
(define (parse-typarams who tp ncls nmth)
  (cond
    [(not tp) '()]
    [else
     (define params
       (for/list ([n (in-list (cdr tp))]) (parse-generic-param who n ncls nmth)))
     (define names (map generic-param-name params))
     (when (check-duplicates names)
       (error 'rangi "~a: duplicate generic parameter ~a" who (check-duplicates names)))
     params]))

; .locals init (...) and .locals (...) are both accepted. An entry is a type, or (TYPE NAME).
; A (class ...), (valuetype ...), (szarray ...) or (array ...) entry is always a bare type, so it
; is never read as a name.
(define (parse-local-var who node ncls nmth)
  (cond
    [(and (pair? node) (memq (car node) '(class valuetype szarray array)))
     (check-type who node ncls nmth)
     (local-var node #f)]
    [(and (list? node) (= (length node) 2) (symbol? (cadr node)))
     (check-type who (car node) ncls nmth)
     (local-var (car node) (cadr node))]
    [else (check-type who node ncls nmth) (local-var node #f)]))

(define (parse-locals who raw ncls nmth)
  (match raw
    [#f #f]
    [(list '.locals 'init (? list? vars))
     (locals-decl #t (parse-local-vars who vars ncls nmth))]
    [(list '.locals (? list? vars))
     (locals-decl #f (parse-local-vars who vars ncls nmth))]
    [_ (error 'rangi "~a: malformed .locals ~s" who raw)]))

(define (parse-local-vars who vars ncls nmth)
  (define parsed (for/list ([v (in-list vars)]) (parse-local-var who v ncls nmth)))
  (define names (filter values (map local-var-name parsed)))
  (when (check-duplicates names)
    (error 'rangi "~a: duplicate local ~a" who (check-duplicates names)))
  parsed)

; .entrypoint, .maxstack, .locals and .try are directives inside a body, so they are lifted
; out of the code. maxstack is #f when there is no .maxstack, so lowering can tell an explicit
; value from the default.
(define (split-directives il)
  (for/fold ([code '()] [maxstack #f] [entry? #f] [raw-locals #f] [handlers '()]
             #:result (values (reverse code) maxstack entry? raw-locals (reverse handlers)))
            ([node (in-list il)])
    (match node
      [(list '.entrypoint) (values code maxstack #t raw-locals handlers)]
      [(list '.maxstack n)
       (unless (and (exact-nonnegative-integer? n) (< n #x10000))
         (error 'rangi "invalid .maxstack ~s" n))
       (values code n entry? raw-locals handlers)]
      [(cons '.locals _)
       (when raw-locals (error 'rangi "duplicate .locals"))
       (values code maxstack entry? node handlers)]
      [(list '.try (list 'catch (list (? symbol? asm) (? symbol? ty)))
             (? symbol? ts) (? symbol? te) (? symbol? hs) (? symbol? he))
       (values code maxstack entry? raw-locals
               (cons (eh-clause 'catch (list asm ty) ts te hs he) handlers))]
      [(list '.try (list (and kind (or 'finally 'fault)))
             (? symbol? ts) (? symbol? te) (? symbol? hs) (? symbol? he))
       (values code maxstack entry? raw-locals
               (cons (eh-clause kind #f ts te hs he) handlers))]
      [(list '.try (list 'filter (? symbol? filter-label))
             (? symbol? ts) (? symbol? te) (? symbol? hs) (? symbol? he))
       (values code maxstack entry? raw-locals
               (cons (eh-clause 'filter filter-label ts te hs he) handlers))]
      [(list '.try _ ...)
       (error 'rangi "malformed .try ~s (expected (.try (catch (asm ty)) try-start try-end handler-start handler-end), (.try (finally) ...), (.try (fault) ...) or (.try (filter filter-label) ...))" node)]
      [_ (values (cons node code) maxstack entry? raw-locals handlers)])))

; The 7-element form has no generic parameters. The 8-element form has a (.typarams ...)
; list before the parameter list. The 5-element form has no body and no implementation flags:
; only an abstract method may omit its body (II.22.26 MethodAttributes Abstract).
(define (parse-method class-name node ncls)
  (define-values (tp prefix ret name params suffix il bodiless?)
    (match node
      [(list '.method prefix ret name params suffix il)
       (values #f prefix ret name params suffix il #f)]
      [(list '.method prefix ret name (and tp (cons '.typarams _)) params suffix il)
       (values tp prefix ret name params suffix il #f)]
      [(list '.method prefix ret name params)
       (values #f prefix ret name params #f #f #t)]
      [_ (error 'rangi "malformed .method in ~a: ~s" class-name node)]))
  (define abstract? (and (memq 'abstract prefix) #t))
  (cond
    [(and bodiless? (not abstract?))
     (error 'rangi "method ~a in ~a has no body; only abstract methods may omit it" name class-name)]
    [(and abstract? (not bodiless?))
     (error 'rangi "abstract method ~a in ~a cannot have a body" name class-name)])
  (unless bodiless?
    (unless (and (list? suffix) (= (length suffix) 2) (memq 'cil suffix) (memq 'managed suffix))
      (error 'rangi "unsupported implementation flags ~s on ~a" suffix name)))
  (unless (list? params) (error 'rangi "malformed parameter list on ~a: ~s" name params))
  (define gparams (parse-typarams name tp ncls (typarams-count tp)))
  (define nmth (length gparams))
  (define-values (code maxstack entry? raw-locals handlers)
    (if bodiless?
        (values #f #f #f #f '())
        (split-directives il)))
  (check-type name ret ncls nmth)
  (for ([p (in-list params)]) (check-type name p ncls nmth))
  (method-decl prefix ret name gparams params code maxstack entry?
               (parse-locals name raw-locals ncls nmth) handlers))

; .override Owner::M ret params, or .override (asm ty) M ret params for a base in another assembly.
(define (parse-override class-name node ncls)
  (define-values (owner name ret params)
    (match node
      [(list '.override (? symbol? qual) ret (? list? params))
       (define m (regexp-match #rx"^([^:]+)::([^:]+)$" (symbol->string qual)))
       (unless m
         (error 'rangi "malformed .override in ~a: ~s (expected Owner::Name)" class-name node))
       (values (string->symbol (cadr m)) (string->symbol (caddr m)) ret params)]
      [(list '.override (list (? symbol?) (? symbol?)) (? symbol? name) ret (? list? params))
       (values (cadr node) name ret params)]
      [_ (error 'rangi "malformed .override in ~a: ~s" class-name node)]))
  (check-type name ret ncls 0)
  (for ([p (in-list params)]) (check-type name p ncls 0))
  (override-decl owner name ret params))

; .implements Iface, or .implements (Assembly Ty) for an interface in another assembly (II.22.23).
; The result is the name as in extends: a symbol, or (Assembly Ty).
(define (parse-implements class-name node)
  (match node
    [(list '.implements (? symbol? iface)) iface]
    [(list '.implements (list (? symbol? asm) (? symbol? ty))) (list asm ty)]
    [_ (error 'rangi "malformed .implements in ~a: ~s" class-name node)]))

; (.field (flags ...) type name) or (.field (flags ...) type name = (prim value)). Field types may
; use the class's type variables !N (II.23.2.12).
(define integral-ranges
  '((int8 -128 . 127) (uint8 0 . 255) (int16 -32768 . 32767) (uint16 0 . 65535)
    (int32 -2147483648 . 2147483647) (uint32 0 . 4294967295)
    (int64 -9223372036854775808 . 9223372036854775807) (uint64 0 . 18446744073709551615)))

; A literal field (II.22.9) is static and has a value; a value is only allowed on a literal.
(define (parse-field class-name node ncls)
  (match node
    [(list '.field (? list? flags) type (? symbol? name))
     (check-type name type ncls 0)
     (when (eq? type 'void) (error 'rangi "field ~a.~a cannot be void" class-name name))
     (when (memq 'literal flags)
       (error 'rangi "literal field ~a.~a needs a value" class-name name))
     (field-decl flags type name #f #f)]
    [(list '.field (? list? flags) type (? symbol? name) '= (list (? symbol? prim) (? exact-integer? v)))
     (check-type name type ncls 0)
     (define range (assq prim integral-ranges))
     (unless range
       (error 'rangi "literal field ~a.~a has non-integral type ~a" class-name name prim))
     (unless (<= (cadr range) v (cddr range))
       (error 'rangi "value ~a out of range for ~a in ~a.~a" v prim class-name name))
     (unless (and (memq 'literal flags) (memq 'static flags))
       (error 'rangi "a value needs a static literal field, ~a.~a is not" class-name name))
     (field-decl flags type name (cons prim v) #f)]
    ; FieldRVA (II.22.18): the field's initial value is the named .data block. The static check
    ; is made in lower, where the FieldRVA row is built.
    [(list '.field (? list? flags) type (? symbol? name) 'at (? symbol? dname))
     (check-type name type ncls 0)
     (when (eq? type 'void) (error 'rangi "field ~a.~a cannot be void" class-name name))
     (when (memq 'literal flags)
       (error 'rangi "literal field ~a.~a cannot have data at ~a" class-name name dname))
     (unless (memq 'static flags)
       (error 'rangi "FieldRVA field ~a.~a must be static" class-name name))
     (field-decl flags type name #f dname)]
    [_ (error 'rangi "malformed .field in ~a: ~s" class-name node)]))

; A .data byte is hex, as in ilasm. Racket reads 10 as the number ten, so each token is read back
; from its printed digits and parsed as hex; 10 gives 16 and 1A stays a symbol.
(define (parse-data-byte dname x)
  (define s (format "~a" x))
  (unless (regexp-match? #px"^[0-9A-Fa-f]{1,2}$" s)
    (error 'rangi "data ~a: ~a is not a hex byte" dname s))
  (string->number s 16))

; .data NAME = bytearray (HEX ...) (II.16): one initialised data block, spelled as ilasm spells it.
; Its length is checked against the field type in check-field-data.
(define (parse-data-decl node)
  (match node
    [(list '.data (? symbol? name) '= (list 'bytearray (? list? items)))
     (data-decl name (apply bytes (for/list ([x (in-list items)]) (parse-data-byte name x))))]
    [_ (error 'rangi "malformed .data: ~s" node)]))

; Byte size of a fixed-size primitive, for checking FieldRVA data (II.23.1.16).
(define primitive-sizes
  '((boolean . 1) (int8 . 1) (uint8 . 1) (char . 2) (int16 . 2) (uint16 . 2)
    (int32 . 4) (uint32 . 4) (float32 . 4) (int64 . 8) (uint64 . 8) (float64 . 8)))

; Each FieldRVA field names a .data block that exists, and a block belongs to one field only.
; A primitive's data must be exactly its size. Valuetype sizes are not known here, so they are
; not checked.
(define (check-field-data f data-decls)
  (define name (field-decl-name f))
  (define dname (field-decl-at f))
  (define d (findf (λ (d) (eq? (data-decl-name d) dname)) data-decls))
  (unless d (error 'rangi "field ~a uses undefined data ~a" name dname))
  (define size (cond [(assq (field-decl-type f) primitive-sizes) => cdr] [else #f]))
  (when (and size (not (= size (bytes-length (data-decl-bytes d)))))
    (error 'rangi "data ~a for field ~a has ~a bytes, ~a needs ~a"
           dname name (bytes-length (data-decl-bytes d)) (field-decl-type f) size)))

; Class clauses between the name and the body: .typarams declares generic parameters, and
; .extends names the base class (II.22.37). Each may appear at most once.
(define (class-clauses name clauses)
  (for/fold ([tp #f] [ext #f] #:result (values tp ext)) ([c (in-list clauses)])
    (match c
      [(cons '.typarams _)
       (when tp (error 'rangi "duplicate .typarams in class ~a" name))
       (values c ext)]
      [(list '.extends base)
       (when ext (error 'rangi "duplicate .extends in class ~a" name))
       (values tp base)]
      [_ (error 'rangi "unsupported class clause ~s in ~a" c name)])))

; .ver M:m:b:r, four parts that each fit in 16 bits (II.22.5 MajorVersion..RevisionNumber)
(define (parse-ref-version who v)
  (define m (and (symbol? v)
                 (regexp-match #px"^([0-9]+):([0-9]+):([0-9]+):([0-9]+)$" (symbol->string v))))
  (unless m (error 'rangi "~a: .ver must be M:m:b:r, got ~s" who v))
  (define parts (map string->number (cdr m)))
  (for ([p (in-list parts)])
    (unless (<= p #xFFFF) (error 'rangi "~a: version part ~a exceeds 65535" who p)))
  parts)

; .publickeytoken = (HEX ...): exactly 8 bytes (II.22.5 PublicKeyOrToken). A token is written as a
; symbol or number, so each element is read back as text and parsed as hex.
(define (parse-ref-token who hex)
  (define bs
    (for/list ([t (in-list hex)])
      (define s (format "~a" t))
      (unless (regexp-match? #px"^[0-9A-Fa-f]{1,2}$" s)
        (error 'rangi "~a: public key token byte ~a is not a hex byte" who s))
      (string->number s 16)))
  (unless (= (length bs) 8)
    (error 'rangi "~a: public key token must be 8 bytes, got ~a" who (length bs)))
  (apply bytes bs))

; The body of .assembly extern: any order of .ver and .publickeytoken, each at most once.
(define (parse-asm-extern-body who body)
  (let loop ([b body] [ver #f] [tok #f])
    (match b
      ['() (values (or ver '(0 0 0 0)) (or tok #""))]
      [(list* '.ver v rest)
       (when ver (error 'rangi "duplicate .ver in .assembly extern ~a" who))
       (loop rest (parse-ref-version who v) tok)]
      [(list* '.publickeytoken '= (? list? hex) rest)
       (when tok (error 'rangi "duplicate .publickeytoken in .assembly extern ~a" who))
       (loop rest ver (parse-ref-token who hex))]
      [_ (error 'rangi "unsupported .assembly extern clause ~s in ~a" b who)])))

; A nested class is a .class node inside a class body (II.10.3). Its simple name may not contain
; . (a namespace separator) or / (the separator of a full name such as Outer/Inner).
(define (nested-class-node? node)
  (and (pair? node) (eq? (car node) '.class)))

; The (flags name tp ext body) shape of a top-level class, for a nested .class node.
(define (nested-class-raw node)
  (match node
    [(list '.class (? list? flags) (? symbol? name) clause ... (? list? body))
     (unless (regexp-match? #rx"^[^./]+$" (symbol->string name))
       (error 'rangi "nested class name ~a may not contain . or /" name))
     (define-values (tp ext) (class-clauses name clause))
     (list flags name tp ext body)]
    [_ (error 'rangi "malformed nested class ~s" node)]))

; A class followed by its nested classes in source order (II.10.3). enclosing is the full name
; of the enclosing class, or #f. A nested class's full name is Outer/Inner.
(define (flatten-class raw enclosing)
  (match-define (list flags simple tp ext body) raw)
  (define name (if enclosing (string->symbol (format "~a/~a" enclosing simple)) simple))
  (define gparams (parse-typarams name tp (typarams-count tp) 0))
  (define ncls (length gparams))
  (define members (filter (λ (node) (not (nested-class-node? node))) body))
  (define fields
    (for/list ([node (in-list members)] #:when (and (pair? node) (eq? (car node) '.field)))
      (parse-field name node ncls)))
  (define overrides
    (for/list ([node (in-list members)] #:when (and (pair? node) (eq? (car node) '.override)))
      (parse-override name node ncls)))
  (define implements
    (for/list ([node (in-list members)] #:when (and (pair? node) (eq? (car node) '.implements)))
      (parse-implements name node)))
  (when (check-duplicates implements)
    (error 'rangi "duplicate .implements ~a in ~a" (check-duplicates implements) name))
  (define methods
    (for/list ([node (in-list members)]
               #:unless (and (pair? node) (memq (car node) '(.field .override .implements))))
      (parse-method name node ncls)))
  (when (check-duplicates (map field-decl-name fields))
    (error 'rangi "duplicate field ~a in ~a" (check-duplicates (map field-decl-name fields)) name))
  (cons (class-decl flags name gparams ext methods fields enclosing overrides implements)
        (append* (for/list ([node (in-list body)] #:when (nested-class-node? node))
                   (flatten-class (nested-class-raw node) name)))))

(define (parse-il program)
  (define asm-refs '())
  (define asm-def? #f)
  (define mod-name #f)
  (define fmt #f)
  (define dll? #f)
  (define subsystem #f)
  (define platform #f)
  (define data-decls '())
  (define (add-asm-extern! filename body)
    (define name (read-assembly-meta (read-file filename)))
    (when (findf (λ (r) (equal? (asm-ref-name r) name)) asm-refs)
      (error 'rangi "duplicate .assembly extern ~a" name))
    (define-values (version token) (parse-asm-extern-body name body))
    (set! asm-refs (cons (asm-ref name version token) asm-refs)))
  (define raw-classes
    (for/fold ([acc '()] #:result (reverse acc)) ([node (in-list program)])
      (match node
        [(list '.assembly 'extern filename)
         (add-asm-extern! filename '())
         acc]
        [(list '.assembly 'extern filename body)
         (add-asm-extern! filename body)
         acc]
        [(list '.assembly _ _)
         (when asm-def? (error 'rangi "only one .assembly directive is allowed"))
         (set! asm-def? #t)
         acc]
        [(list '.module name)
         (when mod-name (error 'rangi "only one .module directive is allowed"))
         (set! mod-name (symbol->string name))
         acc]
        [(list '.format f more ...)
         (when fmt (error 'rangi "only one .format directive is allowed"))
         (unless (memq f '(pe32 pe32+)) (error 'rangi "unknown .format ~a, expected pe32 or pe32+" f))
         (unless (member more '(() (dll))) (error 'rangi "unknown .format option ~s, expected dll" more))
         (set! fmt f)
         (set! dll? (pair? more))
         acc]
        [(list '.subsystem s)
         (when subsystem (error 'rangi "only one .subsystem directive is allowed"))
         (unless (memq s '(console windows))
           (error 'rangi "unknown .subsystem ~a, expected console or windows" s))
         (set! subsystem s)
         acc]
        [(list '.platform p)
         (when platform (error 'rangi "only one .platform directive is allowed"))
         (unless (memq p '(anycpu x86 32bitpreferred))
           (error 'rangi "unknown .platform ~a, expected anycpu, x86, or 32bitpreferred" p))
         (set! platform p)
         acc]
        [(list '.class flags name clause ... body)
         (when (regexp-match? #rx"/" (symbol->string name))
           (error 'rangi "class name ~a may not contain /" name))
         (define-values (tp ext) (class-clauses name clause))
         (cons (list flags name tp ext body) acc)]
        [(list '.data _ '= _)
         (set! data-decls (cons (parse-data-decl node) data-decls))
         acc]
        [_ (error 'rangi "unsupported top-level directive ~s" node)])))

  (when (check-duplicates (map cadr raw-classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map cadr raw-classes))))

  ; <Module> is always TypeDef row 1. Its methods move to a generated Program class,
  ; since the CLR rejects entry points declared on <Module>.
  (define module-cls
    (or (findf (class-named? '<Module>) raw-classes) (list '() '<Module> #f #f '())))
  (when (for/or ([node (in-list (list-ref module-cls 4))])
          (and (pair? node) (memq (car node) '(.override .implements))))
    (error 'rangi "~a is not allowed in <Module>"
           (for/first ([node (in-list (list-ref module-cls 4))]
                       #:when (and (pair? node) (memq (car node) '(.override .implements))))
             (car node))))
  (define others (remove module-cls raw-classes))
  (define module-body (list-ref module-cls 4))
  (when (ormap nested-class-node? module-body)
    (error 'rangi "<Module> cannot have nested classes"))
  (define moved? (pair? module-body))
  (when (and moved? (findf (class-named? 'Program) others))
    (error 'rangi "class Program clashes with the holder generated for <Module> methods"))
  (define ordered
    (append (list (if moved?
                      (list (car module-cls) '<Module> (caddr module-cls) (cadddr module-cls) '())
                      module-cls))
            (if moved? (list (list '() 'Program #f #f module-body)) '())
            others))

  (define classes (append* (for/list ([cls (in-list ordered)]) (flatten-class cls #f))))
  (when (check-duplicates (map class-decl-name classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map class-decl-name classes))))

  (define data-fields
    (for*/list ([c (in-list classes)] [f (in-list (class-decl-fields c))] #:when (field-decl-at f))
      f))
  (when (check-duplicates (map data-decl-name data-decls))
    (error 'rangi "duplicate data ~a" (check-duplicates (map data-decl-name data-decls))))
  (for ([f (in-list data-fields)]) (check-field-data f data-decls))
  (when (check-duplicates (map field-decl-at data-fields))
    (error 'rangi "data ~a is used by more than one field"
           (check-duplicates (map field-decl-at data-fields))))
  (for ([d (in-list data-decls)]
        #:unless (findf (λ (f) (eq? (field-decl-at f) (data-decl-name d))) data-fields))
    (error 'rangi "data ~a is not used by any field" (data-decl-name d)))

  (define entries
    (for*/list ([c (in-list classes)] [m (in-list (class-decl-methods c))] #:when (method-decl-entry? m))
      m))
  ; a DLL may have no entry point (its _CorDllMain stub is the image entry); an EXE needs one
  (unless (or (= (length entries) 1) (and dll? (null? entries)))
    (error 'rangi "exactly one .entrypoint is required, found ~a" (length entries)))

  (module-model (reverse asm-refs) classes mod-name (or fmt 'pe32) dll?
                (or subsystem 'console) (or platform 'anycpu) (reverse data-decls)))
