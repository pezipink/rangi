#lang racket/base
; Array instructions lower to tokens (II.22, III.4). A primitive element type becomes a
; TypeRef to mscorlib (System.<Name>). Void, typedref, and array element types are rejected
; in the element operand of newarr, ldelem, and stelem.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program-with . body-forms)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) ,@body-forms (ret) })]))))

(define (entry-body cp)
  (for*/first ([td (in-list (cli-program-typedefs cp))]
               [md (in-list (tdef-methods td))]
               #:when (mdef-entry? md))
    (mdef-body md)))

; The token is the 4 little-endian bytes after the opcode byte.
(define (operand-after body opcode)
  (define idx (for/first ([i (in-range (bytes-length body))]
                          #:when (= (bytes-ref body i) opcode))
                i))
  (and idx (integer-bytes->integer (subbytes body (add1 idx) (+ idx 5)) #f #f)))

(test-case "newarr int32 uses a TypeRef token to System.Int32"
  (define cp (lower-module (program-with '(ldc.i4.s 10) '(newarr int32) '(pop))))
  (define tok (operand-after (entry-body cp) #x8D))
  (define rid (bitwise-and tok #xFFFFFF))
  (check-equal? (arithmetic-shift tok -24) #x01)
  (define row (list-ref (cli-program-typerefs cp) (sub1 rid)))
  (check-equal? (list (car (list-ref (cli-program-asm-refs cp) (sub1 (car row))))
                      (cadr row) (caddr row))
                (list "mscorlib" "System" "Int32")))

(test-case "a void element type is rejected"
  (check-exn #rx"array element type void is not supported"
             (λ () (lower-module (program-with '(ldc.i4.s 1) '(newarr void) '(pop))))))

(test-case "a typedref element type is rejected"
  (check-exn #rx"array element type typedref is not supported"
             (λ () (lower-module (program-with '(ldc.i4.s 1) '(newarr typedref) '(pop))))))

(test-case "an array element type is rejected in newarr"
  (check-exn #rx"array element type"
             (λ () (lower-module (program-with '(ldc.i4.s 1) '(newarr (szarray int32)) '(pop))))))

(test-case "ldelem and stelem with a primitive type use the same TypeRef as newarr"
  ; arr = newarr 1; arr[0] = 7; x = arr[0]; pop x; pop arr
  (define cp (lower-module (program-with '(ldc.i4.s 1) '(newarr int32)
                                         '(dup) '(ldc.i4.s 0) '(ldc.i4.s 7) '(stelem int32)
                                         '(ldc.i4.s 0) '(ldelem int32) '(pop))))
  (define body (entry-body cp))
  (check-equal? (operand-after body #x8D) (operand-after body #xA4))
  (check-equal? (operand-after body #x8D) (operand-after body #xA3)))

(test-case "the explicit (mscorlib System.Int32) form names the same TypeRef as int32"
  (define a (entry-body (lower-module (program-with '(ldc.i4.s 1) '(newarr int32) '(pop)))))
  (define b (entry-body (lower-module (program-with '(ldc.i4.s 1) '(newarr (mscorlib System.Int32)) '(pop)))))
  (check-equal? (operand-after a #x8D) (operand-after b #x8D)))

(test-case "ldelema with a primitive type lowers to a token"
  ; arr = newarr 1; p = &arr[0]; pop p; pop arr
  (define body (entry-body (lower-module (program-with '(ldc.i4.s 1) '(newarr int32)
                                                       '(dup) '(ldc.i4.s 0) '(ldelema int32) '(pop) '(pop)))))
  (check-equal? (operand-after body #x8F) (operand-after body #x8D)))


