#lang racket/base
(require rackunit
         racket/promise
         "../../src/types/canon.rkt"
         "../../src/types/desc.rkt")

(define int32 (source-primitive "int"))
(define str (source-primitive "string"))
(define list-of-t
  (type-ref "mscorlib" "System.Collections.Generic" "List" 1 'class (list (type-param 'type 0))))

(test-case "subst-type replaces type parameters, including nested ones"
  (check-equal? (subst-type (type-param 'type 0) (list int32)) int32)
  (check-equal? (subst-type list-of-t (list str))
                (type-ref "mscorlib" "System.Collections.Generic" "List" 1 'class (list str)))
  (check-equal? (subst-type (type-ref #f "" "" 0 'szarray (list (type-param 'type 0))) (list int32))
                (type-ref #f "" "" 0 'szarray (list int32)))
  (check-equal? (subst-type 'int32 (list int32)) 'int32))

(test-case "subst-type leaves method-level parameters alone"
  (check-equal? (subst-type (type-param 'method 0) (list int32)) (type-param 'method 0)))

(test-case "subst-type rejects an index with no argument"
  (check-exn exn:fail? (λ () (subst-type (type-param 'type 1) (list int32)))))

(define box-ref (type-ref "Local" "Demo" "Box" 1 'class '()))
(define open-box
  (type-desc box-ref 'class #f #f (delay #f) (delay '())
             (delay (list (method-desc box-ref "Get" #t #f #t #f #f 0 '() (type-param 'type 0))))
             (delay '())))

(test-case "instantiate-desc builds a closed instance without changing the open one"
  (define closed (instantiate-desc open-box (list int32)))
  (define get (car (force (type-desc-methods closed))))
  (check-equal? (type-desc-ref closed) (with-args box-ref (list int32)))
  (check-equal? (type-desc-shape closed) 'class)
  (check-false (force (type-desc-base closed)))
  (check-equal? (method-desc-ret get) int32)
  (check-equal? (method-desc-owner get) (type-desc-ref closed))
  (check-equal? (method-desc-ret (car (force (type-desc-methods open-box)))) (type-param 'type 0)))
