#lang racket/base
(require racket/match
         racket/list
         racket/file
         "../cli-reader.rkt"
         (only-in "../cli/sigs.rkt" primitive-names))
(provide parse-il
         (struct-out module-model)
         (struct-out class-decl)
         (struct-out method-decl)
         (struct-out generic-param)
         (struct-out locals-decl)
         (struct-out local-var))

; The front end's output. It holds names and instructions as written, with no tokens,
; heap indexes, or flag bits. cli/lower.rkt resolves those.
(struct module-model (asm-refs classes module-name format))
(struct class-decl (flags name gparams methods))
(struct method-decl (flags ret name gparams params code maxstack entry? locals))
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
; optional type arguments as a list, which must not be empty. ncls and nmth are the
; number of class and method parameters in scope.
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
    [(list (or 'class 'valuetype) (? symbol?)) (void)]
    [(list (or 'class 'valuetype) (? symbol?) '())
     (error 'rangi "~a: empty generic argument list in ~s" who t)]
    [(list (or 'class 'valuetype) (? symbol?) (? list? args))
     (for ([a (in-list args)]) (check-type who a ncls nmth))]
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
; A (class ...) or (valuetype ...) entry is always a bare type, so it is never read as a name.
(define (parse-local-var who node ncls nmth)
  (cond
    [(and (pair? node) (memq (car node) '(class valuetype)))
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

; .entrypoint, .maxstack and .locals are directives inside a body, so they are lifted out of the code
(define (split-directives il)
  (for/fold ([code '()] [maxstack 8] [entry? #f] [raw-locals #f]
             #:result (values (reverse code) maxstack entry? raw-locals))
            ([node (in-list il)])
    (match node
      [(list '.entrypoint) (values code maxstack #t raw-locals)]
      [(list '.maxstack n)
       (unless (and (exact-nonnegative-integer? n) (< n #x10000))
         (error 'rangi "invalid .maxstack ~s" n))
       (values code n entry? raw-locals)]
      [(cons '.locals _)
       (when raw-locals (error 'rangi "duplicate .locals"))
       (values code maxstack entry? node)]
      [_ (values (cons node code) maxstack entry? raw-locals)])))

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
  (define-values (code maxstack entry? raw-locals) (split-directives il))
  (check-type name ret ncls nmth)
  (for ([p (in-list params)]) (check-type name p ncls nmth))
  (method-decl prefix ret name gparams params code maxstack entry?
               (parse-locals name raw-locals ncls nmth)))

(define (parse-il program)
  (define asm-refs '())
  (define asm-def? #f)
  (define mod-name #f)
  (define fmt #f)
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
        [(list '.format f)
         (when fmt (error 'rangi "only one .format directive is allowed"))
         (unless (memq f '(pe32 pe32+)) (error 'rangi "unknown .format ~a, expected pe32 or pe32+" f))
         (set! fmt f)
         acc]
        [(list '.class flags name body)
         (cons (list flags name #f body) acc)]
        [(list '.class flags name (and tp (cons '.typarams _)) body)
         (cons (list flags name tp body) acc)]
        [_ (error 'rangi "unsupported top-level directive ~s" node)])))

  (when (check-duplicates (map cadr raw-classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map cadr raw-classes))))

  ; <Module> is always TypeDef row 1. Its methods move to a generated Program class,
  ; since the CLR rejects entry points declared on <Module>.
  (define module-cls
    (or (findf (class-named? '<Module>) raw-classes) (list '() '<Module> #f '())))
  (define others (remove module-cls raw-classes))
  (define moved? (pair? (cadddr module-cls)))
  (when (and moved? (findf (class-named? 'Program) others))
    (error 'rangi "class Program clashes with the holder generated for <Module> methods"))
  (define ordered
    (append (list (if moved? (list (car module-cls) '<Module> (caddr module-cls) '()) module-cls))
            (if moved? (list (list '() 'Program #f (cadddr module-cls))) '())
            others))

  (define classes
    (for/list ([cls (in-list ordered)])
      (match-define (list flags name tp body) cls)
      (define gparams (parse-typarams name tp (typarams-count tp) 0))
      (define ncls (length gparams))
      (class-decl flags name gparams
                  (for/list ([node (in-list body)]) (parse-method name node ncls)))))

  (define entries
    (for*/list ([c (in-list classes)] [m (in-list (class-decl-methods c))] #:when (method-decl-entry? m))
      m))
  (unless (= (length entries) 1)
    (error 'rangi "exactly one .entrypoint is required, found ~a" (length entries)))

  (module-model (reverse asm-refs) classes mod-name (or fmt 'pe32)))
