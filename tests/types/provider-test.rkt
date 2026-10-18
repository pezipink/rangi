#lang racket/base
(require rackunit
         racket/promise
         (for-syntax racket/base
                     racket/promise
                     "../../src/types/canon.rkt"
                     "../../src/types/desc.rkt"
                     "../../src/types/provider.rkt")
         "../../src/types/canon.rkt"
         "../../src/types/desc.rkt"
         "../../src/types/provider.rkt"
         "../../src/types/reference.rkt")

; A local type and a local binding that shadows an imported System.Int32.
(define-syntax Point (type-binding (type-ref "Local" "Geo" "Point" 0 'valuetype '())))
(define-syntax Int32 (type-binding (type-ref "Local" "" "Int32" 0 'valuetype '())))

; Resolves a name at expansion time, through a provider holding an imported System.Int32.
(define-syntax (resolved stx)
  (syntax-case stx ()
    [(_ id arity)
     (let* ([other (make-declaration-provider "Other")]
            [e (make-env #:providers (list other) #:opens '("System"))])
       (declare-type! other (type-desc (type-ref "Other" "System" "Int32" 0 'valuetype '())
                                       'valuetype #f #t (delay #f) (delay '()) (delay '()) (delay '())))
       (define r (resolve-type-name e #'id #:arity (syntax-e #'arity)))
       #`(quote #,r))]))

(test-case "a lexical type binding is found during expansion"
  (check-equal? (resolved Point 0) (type-ref "Local" "Geo" "Point" 0 'valuetype '())))

(test-case "a lexical binding wins over an opened type of the same name"
  (check-equal? (resolved Int32 0) (type-ref "Local" "" "Int32" 0 'valuetype '())))

(test-case "an unbound name with no provider match resolves to #f"
  (check-false (resolved Nowhere 0)))

(define (ident s) (datum->syntax #f (string->symbol s)))

(define (point-desc asm)
  (type-desc (type-ref asm "N" "Point" 0 'valuetype '()) 'valuetype #f #t
             (delay #f) (delay '()) (delay '()) (delay '())))

(test-case "the same name in two providers is ambiguous by default"
  (define pa (make-declaration-provider "A"))
  (define pb (make-declaration-provider "B"))
  (declare-type! pa (point-desc "A"))
  (declare-type! pb (point-desc "B"))
  (define e (make-env #:providers (list pa pb) #:opens '("N")))
  (check-exn exn:fail:syntax? (λ () (resolve-type-name e (ident "Point")))))

(test-case "a policy can prefer the local match"
  (define pa (make-declaration-provider "A"))
  (define pb (make-declaration-provider "B"))
  (declare-type! pa (point-desc "A"))
  (declare-type! pb (point-desc "B"))
  (define e (make-env #:providers (list pa pb) #:opens '("N")))
  (check-equal? (resolve-type-name e (ident "Point") #:policy (prefer-local-policy "A"))
                (type-ref "A" "N" "Point" 0 'valuetype '())))

(test-case "first-match picks the first candidate, and local wins over it"
  (define pa (make-declaration-provider "A"))
  (define pb (make-declaration-provider "B"))
  (define pc (make-declaration-provider "C"))
  (declare-type! pa (point-desc "A"))
  (declare-type! pb (point-desc "B"))
  (declare-type! pc (point-desc "C"))
  (define e (make-env #:providers (list pa pb pc) #:opens '("N")))
  (check-equal? (resolve-type-name e (ident "Point") #:policy first-match-policy)
                (type-ref "A" "N" "Point" 0 'valuetype '()))
  (check-equal? (resolve-type-name e (ident "Point")
                                  #:policy (prefer-local-policy "C" first-match-policy))
                (type-ref "C" "N" "Point" 0 'valuetype '()))
  (check-equal? (resolve-type-name e (ident "Point")
                                  #:policy (prefer-local-policy "Z" first-match-policy))
                (type-ref "A" "N" "Point" 0 'valuetype '())))

(test-case "declared types are found and redeclaring replaces them, without caching"
  (define dp (make-declaration-provider "Geo"))
  (define r (type-ref "Geo" "" "Shape" 0 'class '()))
  (define e (make-env #:providers (list dp)))
  (declare-type! dp (type-desc r 'class #f #f (delay #f) (delay '()) (delay '()) (delay '())))
  (check-equal? (type-desc-shape (env-type e r)) 'class)
  (declare-type! dp (type-desc r 'valuetype #f #t (delay #f) (delay '()) (delay '()) (delay '())))
  (check-equal? (type-desc-shape (env-type e r)) 'valuetype))

(test-case "declare-type! rejects a foreign assembly, a closed instance and a non-declaration provider"
  (define dp (make-declaration-provider "Geo"))
  (check-exn exn:fail?
             (λ () (declare-type! dp (type-desc (type-ref "Other" "" "X" 0 'class '()) 'class #f #f
                                                (delay #f) (delay '()) (delay '()) (delay '())))))
  (check-exn exn:fail?
             (λ () (declare-type! dp (type-desc (type-ref "Geo" "" "Box" 1 'class
                                                          (list (source-primitive "int")))
                                                'class #f #f (delay #f) (delay '())
                                                (delay '()) (delay '())))))
  (check-exn exn:fail?
             (λ () (declare-type! (provider "X" (λ (ns n a) #f) (λ (r) #f) #t #f)
                                  (point-desc "X")))))

(test-case "declare-member! appends members in order, and a complete type takes no more"
  (define dp (make-declaration-provider "Geo"))
  (define r (type-ref "Geo" "" "Shape" 0 'class '()))
  (define other (type-ref "Geo" "" "Other" 0 'class '()))
  (define e (make-env #:providers (list dp)))
  (define area (method-desc r "Area" #t #f #t #f #f 0 '() (source-primitive "int")))
  (define count (field-desc r "Count" #t #f (source-primitive "int") #f #f))
  (define scale (method-desc r "Scale" #t #f #t #f #f 0 (list (source-primitive "int")) 'void))
  (declare-type! dp (type-desc r 'class #f #f (delay #f) (delay '()) (delay '()) (delay '())))
  (declare-type! dp (type-desc other 'class #f #f (delay #f) (delay '()) (delay '()) (delay '())))
  (check-equal? (declaration-state dp r) 'declared)
  (declare-member! dp r area)
  (declare-member! dp r count)
  (declare-member! dp r scale)
  (define d (env-type e r))
  (check-equal? (map method-desc-name (force (type-desc-methods d))) '("Area" "Scale"))
  (check-equal? (map field-desc-name (force (type-desc-fields d))) '("Count"))
  (complete-type! dp r)
  (check-equal? (declaration-state dp r) 'complete)
  (check-exn exn:fail? (λ () (declare-member! dp r area)))
  (check-exn exn:fail? (λ () (complete-type! dp (type-ref "Geo" "" "Nope" 0 'class '()))))
  (check-exn exn:fail? (λ () (declare-member! dp other area)))
  (check-false (declaration-state dp (type-ref "Geo" "" "Nope" 0 'class '()))))

(test-case "constructed kinds and unknown assemblies have no descriptor"
  (define dp (make-declaration-provider "Geo"))
  (define e (make-env #:providers (list dp)))
  (check-false (env-type e (type-ref #f "" "" 0 'szarray (list (type-ref "Geo" "" "P" 0 'class '())))))
  (check-false (env-type e (type-ref "Nope" "" "X" 0 'class '()))))

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(when (file-exists? mscorlib-path)
  (define core-env
    (make-env #:providers (list (open-reference-provider mscorlib-path))
              #:opens '("System" "System.Collections.Generic")))

  (test-case "qualified and opened names resolve against the core library"
    (check-equal? (resolve-type-name core-env (ident "System.Int32"))
                  (type-ref "mscorlib" "System" "Int32" 0 'valuetype '()))
    (check-equal? (resolve-type-name core-env (ident "Int32"))
                  (type-ref "mscorlib" "System" "Int32" 0 'valuetype '()))
    (check-equal? (resolve-type-name core-env (ident "List") #:arity 1)
                  (type-ref "mscorlib" "System.Collections.Generic" "List" 1 'class '()))
    (check-false (resolve-type-name core-env (ident "List") #:arity 0))
    (check-false (resolve-type-name core-env (ident "NoSuchType"))))

  (test-case "env-type rejects a wrong number of type arguments"
    (check-exn exn:fail?
               (λ () (env-type core-env
                               (with-args (type-ref "mscorlib" "System.Collections.Generic" "List" 1
                                                    'class '())
                                          (list (source-primitive "int")
                                                (source-primitive "int")))))))

  (test-case "find-methods reaches ToString through the base chain"
    (define list-int
      (with-args (lookup-type core-env "System.Collections.Generic" "List" 1)
                 (list (source-primitive "int"))))
    (define ms (find-methods core-env list-int "ToString"))
    (check-true (pair? ms))
    (check-equal? (type-ref-name (method-desc-owner (car ms))) "Object"))

  (test-case "find-methods drops a base method hidden by an override"
    (define ms (find-methods core-env (lookup-type core-env "System" "String" 0) "ToString"))
    (define no-arg (filter (λ (m) (null? (method-desc-params m))) ms))
    (check-equal? (length no-arg) 1)
    (check-equal? (type-ref-name (method-desc-owner (car no-arg))) "String"))

  (test-case "a type found in more than one provider is listed once"
    (check-equal? (length (find-everywhere core-env "System" "Int32" 0)) 1)))
