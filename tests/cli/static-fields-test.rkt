#lang racket/base
; Static and instance fields of this module (II.22.15, II.22.37). A declared field becomes a Field
; row with a FieldSig, and ldsfld/stsfld/ldfld/stfld resolve to that row's token. The instruction
; must match the field's static-ness and declared type.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; A <Module> entry point with the given body, and a Store class with the given fields.
(define (il-with store-fields . body-forms)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) ,@body-forms (ret) })])
     (.class (public auto ansi) Store [ ,@store-fields ]))))

(define (entry-body cp)
  (for*/first ([td (in-list (cli-program-typedefs cp))]
               [md (in-list (tdef-methods td))]
               #:when (mdef-entry? md))
    (mdef-body md)))

; The token is the 4 little-endian bytes after the first occurrence of the opcode byte.
(define (operand-after body opcode)
  (define idx (for/first ([i (in-range (bytes-length body))]
                          #:when (= (bytes-ref body i) opcode))
                i))
  (and idx (integer-bytes->integer (subbytes body (add1 idx) (+ idx 5)) #f #f)))

(define (store-fields cp)
  (define store
    (findf (λ (td) (equal? (tdef-name td) "Store")) (cli-program-typedefs cp)))
  (tdef-fields store))

(define two-fields
  '((.field (public static) int32 count)
    (.field (public) int32 weight)))

(test-case "a declared field becomes a Field row with static flags and a FieldSig"
  (define cp (lower-module (il-with two-fields '(ldsfld Store count int32) '(pop))))
  (define fs (store-fields cp))
  (check-equal? (map fdef-name fs) '("count" "weight"))
  ; Public | Static (II.23.1.5), and Public alone for the instance field
  (check-equal? (fdef-flags (first fs)) #x16)
  (check-equal? (fdef-flags (second fs)) #x06)
  ; FIELD (0x06) then ELEMENT_TYPE_I4 (0x08) (II.23.2.4)
  (check-equal? (fdef-sig (first fs)) (bytes #x06 #x08)))

(test-case "ldsfld and stsfld encode the Field token (table 0x04)"
  (define body
    (entry-body (lower-module (il-with two-fields
                                       '(ldc.i 1) '(stsfld Store count int32)
                                       '(ldsfld Store count int32) '(pop)))))
  (check-equal? (operand-after body #x80) #x04000001)  ; stsfld
  (check-equal? (operand-after body #x7E) #x04000001)) ; ldsfld

(test-case "a field of this module's own class type is a CLASS signature"
  (define cp
    (lower-module (il-with '((.field (public static) (class Store) next))
                           '(ldnull) '(stsfld Store next (class Store)))))
  (check-equal? (fdef-sig (first (store-fields cp))) (bytes #x06 #x12 #x0C)))

(test-case "static instructions reject instance fields, and instance ones reject static fields"
  (check-exn exn:fail?
             (λ () (lower-module (il-with two-fields '(ldc.i 1) '(stsfld Store weight int32)))))
  (check-exn exn:fail?
             (λ () (lower-module (il-with two-fields '(ldnull) '(ldfld Store count int32)))))
  (check-exn exn:fail?
             (λ () (lower-module (il-with two-fields '(ldnull) '(stfld Store count int32))))))

(test-case "a field access must name the declared type and an existing field"
  (check-exn exn:fail?
             (λ () (lower-module (il-with two-fields '(ldsfld Store count string)))))
  (check-exn exn:fail?
             (λ () (lower-module (il-with two-fields '(ldsfld Store missing int32))))))

(test-case "duplicate and void fields are rejected"
  (check-exn exn:fail?
             (λ () (il-with '((.field (public static) int32 count)
                              (.field (public static) int32 count)))))
  (check-exn exn:fail?
             (λ () (il-with '((.field (public static) void count))))))
