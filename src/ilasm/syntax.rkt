#lang racket/base
(require racket/match
         racket/list
         racket/file
         "../cli-reader.rkt"
         (only-in "../cli/sigs.rkt" primitive-names))
(provide parse-il
         tyvar-ref
         (struct-out module-model)
         (struct-out class-decl)
         (struct-out field-decl)
         (struct-out method-decl)
         (struct-out generic-param)
         (struct-out locals-decl)
         (struct-out local-var)
         (struct-out eh-clause))

; The front end's output. It holds names and instructions as written, with no tokens,
; heap indexes, or flag bits. cli/lower.rkt resolves those.
; subsystem is 'console (the default) or 'windows (.subsystem). platform is 'anycpu (the default),
; 'x86, or '32bitpreferred (.platform). Both are names here; lower and image map them to flags.
(struct module-model (asm-refs classes module-name format dll? subsystem platform))
; extends is the base type as written: a bare symbol for a class in this module, (asm ty) for an
; external class, or #f for the default System.Object (II.22.37).
(struct class-decl (flags name gparams extends methods fields))
; A field (II.22.15). flags are FieldAttributes keywords; type is a type form (II.22.15).
; init is #f, or (prim . value) for a literal field: an integral primitive and its integer value.
(struct field-decl (flags type name init) #:transparent)
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
; A (class ...), (valuetype ...) or (szarray ...) entry is always a bare type, so it is never
; read as a name.
(define (parse-local-var who node ncls nmth)
  (cond
    [(and (pair? node) (memq (car node) '(class valuetype szarray)))
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
; list before the parameter list.
(define (parse-method class-name node ncls)
  (define-values (tp prefix ret name params suffix il)
    (match node
      [(list '.method prefix ret name params suffix il)
       (values #f prefix ret name params suffix il)]
      [(list '.method prefix ret name (and tp (cons '.typarams _)) params suffix il)
       (values tp prefix ret name params suffix il)]
      [_ (error 'rangi "malformed .method in ~a: ~s" class-name node)]))
  (unless (and (list? suffix) (= (length suffix) 2) (memq 'cil suffix) (memq 'managed suffix))
    (error 'rangi "unsupported implementation flags ~s on ~a" suffix name))
  (unless (list? params) (error 'rangi "malformed parameter list on ~a: ~s" name params))
  (define gparams (parse-typarams name tp ncls (typarams-count tp)))
  (define nmth (length gparams))
  (define-values (code maxstack entry? raw-locals handlers) (split-directives il))
  (check-type name ret ncls nmth)
  (for ([p (in-list params)]) (check-type name p ncls nmth))
  (method-decl prefix ret name gparams params code maxstack entry?
               (parse-locals name raw-locals ncls nmth) handlers))

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
     (field-decl flags type name #f)]
    [(list '.field (? list? flags) type (? symbol? name) '= (list (? symbol? prim) (? exact-integer? v)))
     (check-type name type ncls 0)
     (define range (assq prim integral-ranges))
     (unless range
       (error 'rangi "literal field ~a.~a has non-integral type ~a" class-name name prim))
     (unless (<= (cadr range) v (cddr range))
       (error 'rangi "value ~a out of range for ~a in ~a.~a" v prim class-name name))
     (unless (and (memq 'literal flags) (memq 'static flags))
       (error 'rangi "a value needs a static literal field, ~a.~a is not" class-name name))
     (field-decl flags type name (cons prim v))]
    [_ (error 'rangi "malformed .field in ~a: ~s" class-name node)]))

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

(define (parse-il program)
  (define asm-refs '())
  (define asm-def? #f)
  (define mod-name #f)
  (define fmt #f)
  (define dll? #f)
  (define subsystem #f)
  (define platform #f)
  (define raw-classes
    (for/fold ([acc '()] #:result (reverse acc)) ([node (in-list program)])
      (match node
        [(list '.assembly 'extern filename _)
         (define name (read-assembly-meta (read-file filename)))
         (when (member name asm-refs)
           (error 'rangi "duplicate .assembly extern ~a" name))
         (set! asm-refs (cons name asm-refs))
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
         (define-values (tp ext) (class-clauses name clause))
         (cons (list flags name tp ext body) acc)]
        [_ (error 'rangi "unsupported top-level directive ~s" node)])))

  (when (check-duplicates (map cadr raw-classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map cadr raw-classes))))

  ; <Module> is always TypeDef row 1. Its methods move to a generated Program class,
  ; since the CLR rejects entry points declared on <Module>.
  (define module-cls
    (or (findf (class-named? '<Module>) raw-classes) (list '() '<Module> #f #f '())))
  (define others (remove module-cls raw-classes))
  (define module-body (list-ref module-cls 4))
  (define moved? (pair? module-body))
  (when (and moved? (findf (class-named? 'Program) others))
    (error 'rangi "class Program clashes with the holder generated for <Module> methods"))
  (define ordered
    (append (list (if moved?
                      (list (car module-cls) '<Module> (caddr module-cls) (cadddr module-cls) '())
                      module-cls))
            (if moved? (list (list '() 'Program #f #f module-body)) '())
            others))

  (define classes
    (for/list ([cls (in-list ordered)])
      (match-define (list flags name tp ext body) cls)
      (define gparams (parse-typarams name tp (typarams-count tp) 0))
      (define ncls (length gparams))
      (define fields
        (for/list ([node (in-list body)] #:when (and (pair? node) (eq? (car node) '.field)))
          (parse-field name node ncls)))
      (define methods
        (for/list ([node (in-list body)] #:unless (and (pair? node) (eq? (car node) '.field)))
          (parse-method name node ncls)))
      (when (check-duplicates (map field-decl-name fields))
        (error 'rangi "duplicate field ~a in ~a" (check-duplicates (map field-decl-name fields)) name))
      (class-decl flags name gparams ext methods fields)))

  (define entries
    (for*/list ([c (in-list classes)] [m (in-list (class-decl-methods c))] #:when (method-decl-entry? m))
      m))
  ; a DLL may have no entry point (its _CorDllMain stub is the image entry); an EXE needs one
  (unless (or (= (length entries) 1) (and dll? (null? entries)))
    (error 'rangi "exactly one .entrypoint is required, found ~a" (length entries)))

  (module-model (reverse asm-refs) classes mod-name (or fmt 'pe32) dll?
                (or subsystem 'console) (or platform 'anycpu)))
