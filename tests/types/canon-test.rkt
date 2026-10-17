#lang racket/base
(require rackunit
         "../../src/types/canon.rkt")

(test-case "source spellings of primitives reduce to the metadata reference"
  (define int32 (type-ref "mscorlib" "System" "Int32" 0 'valuetype '()))
  (check-equal? (source-primitive "int") int32)
  (check-equal? (source-primitive "int32") int32)
  (check-equal? (source-primitive "string")
                (type-ref "mscorlib" "System" "String" 0 'class '()))
  (check-equal? (source-primitive "bool")
                (type-ref "mscorlib" "System" "Boolean" 0 'valuetype '())))

(test-case "non-primitive spellings are not primitives"
  (check-false (source-primitive "Foo"))
  (check-false (source-primitive "System.Int32"))
  (check-false (source-primitive "void")))

(test-case "primitive names are recognised by namespace and name"
  (check-true (primitive-name? "System" "Int32"))
  (check-false (primitive-name? "System.Collections.Generic" "List"))
  (check-false (primitive-ref 'void)))

(test-case "type->string gives a readable form"
  (check-equal? (type->string (source-primitive "int")) "System.Int32")
  (check-equal? (type->string (type-param 'type 0)) "!0")
  (check-equal? (type->string (type-param 'method 1)) "!!1")
  (check-equal?
   (type->string (with-args (type-ref "mscorlib" "System.Collections.Generic" "List" 1 'class '())
                            (list (source-primitive "int"))))
   "System.Collections.Generic.List<System.Int32>"))

(test-case "with-args and with-asm copy the other fields"
  (define int32 (source-primitive "int"))
  (check-equal? (with-asm int32 "Other") (type-ref "Other" "System" "Int32" 0 'valuetype '()))
  (check-equal? (with-args int32 (list int32))
                (type-ref "mscorlib" "System" "Int32" 0 'valuetype (list int32))))

(test-case "the facades that stand in for mscorlib are listed"
  (check-equal? core-asm "mscorlib")
  (check-true (and (member "System.Runtime" core-facades) #t)))
