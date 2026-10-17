#lang racket/base
(require racket/match
         racket/list
         racket/file
         "../cli-reader.rkt")
(provide parse-il
         (struct-out module-model)
         (struct-out class-decl)
         (struct-out method-decl))

; The front end's output. It holds names and instructions as written, with no tokens,
; heap indexes, or flag bits. cli/lower.rkt resolves those.
(struct module-model (asm-refs classes module-name format))
(struct class-decl (flags name methods))
(struct method-decl (flags ret name params code maxstack entry?))

(define (class-named? sym)
  (lambda (c) (eq? (cadr c) sym)))

; .entrypoint and .maxstack are directives inside a body, so they are lifted out of the code
(define (split-directives il)
  (for/fold ([code '()] [maxstack 8] [entry? #f]
             #:result (values (reverse code) maxstack entry?))
            ([node (in-list il)])
    (match node
      [(list '.entrypoint) (values code maxstack #t)]
      [(list '.maxstack n)
       (unless (and (exact-nonnegative-integer? n) (< n #x10000))
         (error 'rangi "invalid .maxstack ~s" n))
       (values code n entry?)]
      [_ (values (cons node code) maxstack entry?)])))

(define (parse-method class-name node)
  (match node
    [(list '.method prefix ret name params suffix il)
     (unless (and (list? suffix) (= (length suffix) 2) (memq 'cil suffix) (memq 'managed suffix))
       (error 'rangi "unsupported implementation flags ~s on ~a" suffix name))
     (define-values (code maxstack entry?) (split-directives il))
     (method-decl prefix ret name params code maxstack entry?)]
    [_ (error 'rangi "malformed .method in ~a: ~s" class-name node)]))

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
         (cons (list flags name body) acc)]
        [_ (error 'rangi "unsupported top-level directive ~s" node)])))

  (when (check-duplicates (map cadr raw-classes))
    (error 'rangi "duplicate class name ~a" (check-duplicates (map cadr raw-classes))))

  ; <Module> is always TypeDef row 1. Its methods move to a generated Program class,
  ; since the CLR rejects entry points declared on <Module>.
  (define module-cls
    (or (findf (class-named? '<Module>) raw-classes) (list '() '<Module> '())))
  (define others (remove module-cls raw-classes))
  (define moved? (pair? (caddr module-cls)))
  (when (and moved? (findf (class-named? 'Program) others))
    (error 'rangi "class Program clashes with the holder generated for <Module> methods"))
  (define ordered
    (append (list (if moved? (list (car module-cls) '<Module> '()) module-cls))
            (if moved? (list (list '() 'Program (caddr module-cls))) '())
            others))

  (define classes
    (for/list ([cls (in-list ordered)])
      (match-define (list flags name body) cls)
      (class-decl flags name (for/list ([node (in-list body)]) (parse-method name node)))))

  (define entries
    (for*/list ([c (in-list classes)] [m (in-list (class-decl-methods c))] #:when (method-decl-entry? m))
      m))
  (unless (= (length entries) 1)
    (error 'rangi "exactly one .entrypoint is required, found ~a" (length entries)))

  (module-model (reverse asm-refs) classes mod-name (or fmt 'pe32)))
