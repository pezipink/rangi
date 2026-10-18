#lang racket/base
; Providers and the environment (layer 2 of docs/plans/types.md). A provider knows the types of
; one assembly. The env holds the providers, the namespaces the module opens, and a cache of
; closed generic instances. This file does not read metadata: reference.rkt does.
(require racket/list
         racket/promise
         "canon.rkt"
         "desc.rkt")
(provide (struct-out provider)
         (struct-out env)
         make-env
         provider-for
         env-type
         lookup-type
         find-everywhere
         (struct-out type-binding)
         resolve-type-name
         error-on-ambiguity
         first-match-policy
         prefer-local-policy
         find-methods
         make-declaration-provider
         declare-type!
         declare-member!
         complete-type!
         declaration-state)

; asm: the assembly identity this provider answers for.
; find: (ns name arity) -> open type-desc or #f.
; by-ref: open reference -> open type-desc or #f. Used by env-type.
; cacheable?: #t when the provider's answers never change, so env-type may cache them.
; declare: for declaration providers, (op arg ... -> any) for the ops in make-declaration-provider,
; otherwise #f.
(struct provider (asm find by-ref cacheable? declare))

; providers: a list, so iteration order is deterministic.
; opens: namespace strings, in the order the module opened them.
; cache: closed references -> descriptors, for cacheable providers.
(struct env (providers opens cache))

(define (make-env #:providers [providers '()] #:opens [opens '()])
  (env providers opens (make-hash)))

; The provider for an assembly. The core library is also answered by its facades, when no
; provider names it exactly.
(define (provider-for e asm)
  (define ps (env-providers e))
  (or (findf (λ (p) (equal? (provider-asm p) asm)) ps)
      (and (equal? asm core-asm)
           (findf (λ (p) (member (provider-asm p) core-facades)) ps))))

; A nested type is named with its outer type's arguments too, so it may carry more arguments than its
; own arity (List<int>.Enumerator carries int). The outer's arity is not known here, so only the
; lower bound is checked for nested names.
(define (build p r)
  (define args (type-ref-args r))
  (define open ((provider-by-ref p) (with-args r '())))
  (define arity (type-ref-arity r))
  (define nested? (regexp-match? #rx"/" (type-ref-name r)))
  (define n (length args))
  (cond
    [(not open) #f]
    [(null? args) open]
    [(if nested? (>= n arity) (= n arity)) (instantiate-desc open args)]
    [else (error 'env-type "~a takes ~a type arguments, given ~a"
                 (type-ref-name r) arity n)]))

; The descriptor for a reference, closed if it has arguments. #f when no provider owns the
; assembly, or the reference is a constructed kind (array, pointer, byref), which has no members.
(define (env-type e r)
  (define asm (type-ref-asm r))
  (define p (and asm (provider-for e asm)))
  (cond
    [(not p) #f]
    [(provider-cacheable? p) (hash-ref! (env-cache e) r (λ () (build p r)))]
    [else (build p r)]))

; The open reference of a type named in any provider, or #f.
(define (lookup-type e ns name arity)
  (for/or ([p (in-list (env-providers e))])
    (let ([d ((provider-find p) ns name arity)])
      (and d (type-desc-ref d)))))

(define (ref-key r)
  (list (type-ref-namespace r) (type-ref-name r) (type-ref-arity r)))

; The references of a type found in any provider, in provider order. A type forwarded to an
; assembly that is not in the env is not found: forwarders need that assembly loaded.
(define (find-everywhere e ns name arity)
  (remove-duplicates
   (for*/list ([p (in-list (env-providers e))]
               [d (in-value ((provider-find p) ns name arity))]
               #:when d)
     (type-desc-ref d))))
; The binding a local type gets in its module's scope: (define-syntax Point (type-binding 'ref)).
; Expanding the name as an expression is an error, since a type is not a value.
(struct type-binding (ref)
  #:property prop:procedure
  (λ (self stx) (raise-syntax-error #f "a type name cannot be used as an expression" stx)))

; The type binding of an identifier in the current expansion, if any.
(define (lexical-type id arity)
  (and (syntax-transforming?)
       (let ([v (syntax-local-value id (λ () #f))])
         (and (type-binding? v)
              (= (type-ref-arity (type-binding-ref v)) arity)
              (type-binding-ref v)))))

(define qualified-rx #rx"^(.+)\\.([^.]+)$")

; Lexical binding first, then the qualified name, then each opened namespace. Returns the
; reference, or #f when nothing matches. Several matches go to the policy.
(define (resolve-type-name e id #:arity [arity 0] #:policy [policy error-on-ambiguity])
  (cond
    [(lexical-type id arity) => values]
    [else
     (define refs (candidates e (symbol->string (syntax-e id)) arity))
     (cond
       [(null? refs) #f]
       [(null? (cdr refs)) (car refs)]
       [else (policy id refs)])]))

(define (candidates e text arity)
  (define m (regexp-match qualified-rx text))
  (define qual (and m (cadr m)))
  (define short (if m (caddr m) text))
  (define qualified (if qual (find-everywhere e qual short arity) '()))
  (if (pair? qualified)
      qualified
      (remove-duplicates
       (append* (for/list ([o (in-list (env-opens e))])
                  (find-everywhere e (if qual (string-append o "." qual) o) short arity))))))

(define (error-on-ambiguity id refs)
  (raise-syntax-error #f (format "ambiguous type name ~a: ~a"
                                 (syntax-e id)
                                 (join-strings (map type->string refs) ", "))
                      id))

; Takes the first candidate. Candidates come in provider and open-namespace order, so the choice
; is deterministic.
(define (first-match-policy id refs)
  (car refs))

; Prefers the single match from the given assembly (local types shadow imported ones). When the
; local rule does not apply, the fallback policy decides.
(define (prefer-local-policy asm [fallback error-on-ambiguity])
  (λ (id refs)
    (define locals (filter (λ (r) (equal? (type-ref-asm r) asm)) refs))
    (if (and (pair? locals) (null? (cdr locals)))
        (car locals)
        (fallback id refs))))

; The methods named name, declared by r or any base, most derived first. A method hides a base
; method with the same name and parameter types (an override, or a new declaration). The return
; type is not part of the match. A base that cannot be found ends the walk silently.
(define (find-methods e r name)
  (let loop ([r r] [seen '()])
    (define d (and r (env-type e r)))
    (cond
      [(not d) '()]
      [else
       (define here
         (for/list ([m (in-list (force (type-desc-methods d)))]
                    #:when (equal? (method-desc-name m) name)
                    #:unless (for/or ([s (in-list seen)]) (same-signature? s m)))
           m))
       (append here (loop (force (type-desc-base d)) (append seen here)))])))

; II.8.10.1 and II.22.26: a derived method with the same name and parameter types hides the base
; method. The arity is compared too, because generic method arity is part of its identity.
(define (same-signature? a b)
  (and (= (method-desc-arity a) (method-desc-arity b))
       (equal? (method-desc-params a) (method-desc-params b))))


; A declared type. It is 'declared while members may still be added, and 'complete once sealed.
(struct decl (desc complete?) #:mutable)

; A provider whose types are added by pass 1 of the module being compiled. Its answers are not
; cacheable, because declarations can change between expansions. Its declare procedure takes an
; op and its arguments: 'declare a type-desc, 'member an owner reference and a method or field,
; 'complete a reference, or 'state of a reference.
(define (make-declaration-provider asm)
  (define table (make-hash)) ; ref-key -> decl. Only looked up by key, never iterated.
  (define (find-decl r) (hash-ref table (ref-key r) #f))
  (define (find-open-desc r) (let ([x (find-decl r)]) (and x (decl-desc x))))
  (provider asm
            (λ (ns name arity) (let ([x (hash-ref table (list ns name arity) #f)]) (and x (decl-desc x))))
            find-open-desc
            #f
            (λ (op . args)
              (case op
                [(declare)
                 (define d (car args))
                 (hash-set! table (ref-key (type-desc-ref d)) (decl d #f))]
                [(member)
                 (define owner (car args))
                 (define m (cadr args))
                 (define x (or (find-decl owner)
                               (error 'declare-member! "~a is not declared" (type->string owner))))
                 (when (decl-complete? x)
                   (error 'declare-member! "~a is complete" (type->string owner)))
                 (define d (decl-desc x))
                 (set-decl-desc!
                  x
                  (cond
                    [(and (method-desc? m) (equal? (method-desc-owner m) owner))
                     (struct-copy type-desc d
                                  [methods (delay (append (force (type-desc-methods d)) (list m)))])]
                    [(and (field-desc? m) (equal? (field-desc-owner m) owner))
                     (struct-copy type-desc d
                                  [fields (delay (append (force (type-desc-fields d)) (list m)))])]
                    [else (error 'declare-member! "~a is not a member of ~a"
                                 (if (method-desc? m) (method-desc-name m) (field-desc-name m))
                                 (type->string owner))]))]
                [(complete)
                 (define x (or (find-decl (car args))
                               (error 'complete-type! "~a is not declared" (type->string (car args)))))
                 (set-decl-complete?! x #t)]
                [(state)
                 (let ([x (find-decl (car args))])
                   (and x (if (decl-complete? x) 'complete 'declared)))]
                [else (error 'declaration-provider "unknown op ~a" op)]))))

(define (check-declaration-provider who p)
  (unless (provider-declare p)
    (raise-argument-error who "declaration provider" p)))

; Adds an open type to a declaration provider. A later declaration of the same name replaces it,
; and the new declaration starts 'declared.
(define (declare-type! p d)
  (define r (type-desc-ref d))
  (check-declaration-provider 'declare-type! p)
  (unless (equal? (type-ref-asm r) (provider-asm p))
    (error 'declare-type! "~a belongs to assembly ~a, not ~a"
           (type->string r) (type-ref-asm r) (provider-asm p)))
  (unless (null? (type-ref-args r))
    (error 'declare-type! "~a is a closed instance; declare the open type" (type->string r)))
  ((provider-declare p) 'declare d))

; Appends a method or field to a declared type, so members keep their declaration order. The owner
; must be declared in p and not yet complete.
(define (declare-member! p owner m)
  (check-declaration-provider 'declare-member! p)
  ((provider-declare p) 'member owner m))

; Marks a declared type complete. Its members can no longer change.
(define (complete-type! p r)
  (check-declaration-provider 'complete-type! p)
  ((provider-declare p) 'complete r))

; 'declared, 'complete, or #f when p does not declare r.
(define (declaration-state p r)
  (check-declaration-provider 'declaration-state p)
  ((provider-declare p) 'state r))
