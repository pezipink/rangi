#lang racket/base
(require rackunit
         racket/list
         racket/promise
         "../../src/types/canon.rkt"
         "../../src/types/desc.rkt"
         "../../src/types/provider.rkt"
         "../../src/types/reference.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define have-mscorlib? (file-exists? mscorlib-path))

(define e
  (and have-mscorlib?
       (make-env #:providers (list (open-reference-provider mscorlib-path)))))

(define (get en ns name arity)
  (env-type en (lookup-type en ns name arity)))

(define (members-named d name)
  (filter (λ (m) (equal? (method-desc-name m) name)) (force (type-desc-methods d))))

(when e
  (test-case "value types, classes and sealed flags come from the header"
    (define int-d (get e "System" "Int32" 0))
    (check-equal? (type-desc-shape int-d) 'valuetype)
    (check-equal? (type-ref-kind (type-desc-ref int-d)) 'valuetype)
    (check-true (type-desc-sealed? int-d))
    (define obj (get e "System" "Object" 0))
    (check-equal? (type-desc-shape obj) 'class)
    (check-false (force (type-desc-base obj)))
    (check-true (type-desc-sealed? (get e "System" "String" 0))))

  (test-case "interfaces and enums are classified"
    (define ilist (get e "System.Collections.Generic" "IList" 1))
    (check-equal? (type-desc-shape ilist) 'interface)
    (check-false (force (type-desc-base ilist)))
    (define day (get e "System" "DayOfWeek" 0))
    (check-equal? (type-desc-shape day) 'enum)
    (check-equal? (type-ref-name (force (type-desc-base day))) "Enum"))

  (test-case "a static public field is found with its type"
    (define fields (filter (λ (f) (equal? (field-desc-name f) "MaxValue"))
                           (force (type-desc-fields (get e "System" "Int32" 0)))))
    (check-equal? (length fields) 1)
    (check-true (field-desc-static? (car fields)))
    (check-true (field-desc-public? (car fields)))
    (check-equal? (field-desc-type (car fields)) (source-primitive "int"))
    (check-true (field-desc-literal? (car fields)))
    (check-equal? (field-desc-value (car fields)) 2147483647))

  (test-case "literal values decode by their element type"
    (define (field owner name)
      (findf (λ (f) (equal? (field-desc-name f) name))
             (force (type-desc-fields (get e "System" owner 0)))))
    (check-equal? (field-desc-value (field "Byte" "MaxValue")) 255)
    (check-equal? (field-desc-value (field "Int64" "MinValue")) -9223372036854775808)
    (check-equal? (field-desc-value (field "Char" "MaxValue")) #xFFFF)
    (check-equal? (field-desc-value (field "Double" "NaN")) +nan.0)
    (check-equal? (field-desc-value (field "DayOfWeek" "Monday")) 1)
    (check-true (field-desc-literal? (field "Math" "PI")))
    (check-false (field-desc-literal? (field "DateTime" "MinValue")))
    (check-false (field-desc-value (field "DateTime" "MinValue"))))

  (test-case "List<int> has members substituted from its argument"
    (define list-int
      (with-args (lookup-type e "System.Collections.Generic" "List" 1) (list (source-primitive "int"))))
    (define ld (env-type e list-int))
    (check-equal? (type-desc-ref ld) list-int)
    (check-equal? (map method-desc-params (members-named ld "Add")) (list (list (source-primitive "int"))))
    (check-equal? (method-desc-owner (car (members-named ld "Add"))) list-int)
    (check-equal? (method-desc-ret (car (members-named ld "get_Count"))) (source-primitive "int"))
    (check-equal? (method-desc-params (car (members-named ld "get_Item"))) (list (source-primitive "int")))
    (check-equal? (method-desc-ret (car (members-named ld "get_Item"))) (source-primitive "int")))

  (test-case "method-level type parameters are kept, not substituted"
    (define convert (car (members-named (get e "System.Collections.Generic" "List" 1) "ConvertAll")))
    (check-equal? (method-desc-arity convert) 1)
    (check-equal? (type-ref-args (method-desc-ret convert)) (list (type-param 'method 0))))

  (test-case "a nested type reached through a member is closed over the outer's argument"
    (define ld (env-type e (with-args (lookup-type e "System.Collections.Generic" "List" 1)
                                      (list (source-primitive "int")))))
    (define enumerator (method-desc-ret (car (members-named ld "GetEnumerator"))))
    (check-equal? (type-ref-name enumerator) "List/Enumerator")
    (check-equal? (type-ref-args enumerator) (list (source-primitive "int")))
    (check-equal? (type-ref-kind enumerator) 'valuetype)
    (define nested (env-type e enumerator))
    (check-equal? (map method-desc-ret (members-named nested "get_Current")) (list (source-primitive "int"))))

  (test-case "lookup respects the generic arity suffix"
    (check-false (lookup-type e "System" "Int32" 1))
    (check-false (lookup-type e "System.Collections.Generic" "List" 0))
    (check-false (lookup-type e "System" "NoSuchType" 0)))

  (test-case "descriptors are read lazily: members are decoded only when forced, once each"
    (define fresh (make-env #:providers (list (open-reference-provider mscorlib-path))))
    (reset-reference-decode-count!)
    (define s (get fresh "System" "String" 0))
    (check-equal? (reference-decode-count) 0)
    (define methods (force (type-desc-methods s)))
    (check-equal? (reference-decode-count) (length methods))
    (force (type-desc-methods s))
    (check-equal? (reference-decode-count) (length methods))
    (define fields (force (type-desc-fields s)))
    (check-equal? (reference-decode-count) (+ (length methods) (length fields))))

  (test-case "a declaration with the same members as a reference type gives the same members"
    (define ref-d (get e "System" "Int32" 0))
    (define r (type-desc-ref ref-d))
    (define dp (make-declaration-provider (type-ref-asm r)))
    (declare-type! dp (type-desc r (type-desc-shape ref-d) (type-desc-abstract? ref-d)
                                 (type-desc-sealed? ref-d) (type-desc-base ref-d)
                                 (type-desc-interfaces ref-d) (delay '()) (delay '())))
    (for ([m (in-list (force (type-desc-methods ref-d)))]) (declare-member! dp r m))
    (for ([f (in-list (force (type-desc-fields ref-d)))]) (declare-member! dp r f))
    (complete-type! dp r)
    (define decl-d (env-type (make-env #:providers (list dp)) r))
    (check-equal? (force (type-desc-methods decl-d)) (force (type-desc-methods ref-d)))
    (check-equal? (force (type-desc-fields decl-d)) (force (type-desc-fields ref-d)))))

