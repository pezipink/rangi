#lang racket/base
; Literal fields (II.22.9) carry a Constant row, so each value must match its field type and fit it.
; An enum (II.14.3) has an instance value__ field whose type is the type of its literals.
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (module-with . classes)
  (lower-module
   (parse-il
    `((.assembly extern ,mscorlib-path {})
      (.assembly enums {})
      (.module enums.exe)
      (.class (private auto ansi) <Module>
        [(.method (public static) void main () (cil managed)
           { (.entrypoint) (.maxstack 8) (ret) })])
      ,@classes))))

(define (enum-class . fields)
  `(.class (public sealed auto ansi) Color
     (.extends (mscorlib System.Enum))
     [,@fields]))

(define value-field '(.field (public specialname rtspecialname) int32 value__))

(test-case "a valid enum with negative and positive literals lowers"
  (check-not-exn
   (λ () (module-with
          (enum-class value-field
                      '(.field (public static literal) (valuetype Color) Neg = (int32 -1))
                      '(.field (public static literal) (valuetype Color) Blue = (int32 2)))))))

(test-case "a literal field must have a value"
  (check-exn #rx"literal field Color.X needs a value"
             (λ () (module-with (enum-class value-field
                                            '(.field (public static literal) int32 X))))))

(test-case "a value needs a static literal field"
  (check-exn #rx"a value needs a static literal field"
             (λ () (module-with (enum-class value-field
                                            '(.field (public static) int32 X = (int32 1))))))
  (check-exn #rx"a value needs a static literal field"
             (λ () (module-with (enum-class value-field
                                            '(.field (public literal) int32 X = (int32 1)))))))

(test-case "only integral primitives can be literal constants"
  (check-exn #rx"non-integral type float64"
             (λ () (module-with (enum-class value-field
                                            '(.field (public static literal) float64 X = (float64 1)))))))

(test-case "a literal value must fit its declared type"
  (check-exn #rx"value 300 out of range for int8"
             (λ () (module-with (enum-class value-field
                                            '(.field (public static literal) int8 X = (int8 300)))))))

(test-case "a literal's value type must match its field type"
  (check-exn #rx"literal field X has type int32 but its value is int8"
             (λ () (module-with (enum-class value-field
                                            '(.field (public static literal) int32 X = (int8 1)))))))

(test-case "an enum's value__ must have the same type as its literals"
  (check-exn #rx"enum Color must have an instance value__ of type int32"
             (λ () (module-with
                    (enum-class '(.field (public specialname rtspecialname) int64 value__)
                                '(.field (public static literal) (valuetype Color) Red = (int32 0)))))))
