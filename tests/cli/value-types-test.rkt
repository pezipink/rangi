#lang racket/base
; Value types are classes that extend System.ValueType (II.8.2, II.22.37). A value type's base
; must follow the same extends rules as any class. initobj takes a type token (III.4.10), and a
; class declared in this module names a TypeDef (II.22.37), not a TypeRef.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly value-types-test {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed)
         { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define value-type-pair
  '(.class (public sequential ansi sealed) Pair
     (.extends (mscorlib System.ValueType))
     [(.field (public) int32 first)]))

(define (run-body cp)
  (for*/first ([td (in-list (cli-program-typedefs cp))]
               [md (in-list (tdef-methods td))]
               #:when (equal? (mdef-name md) "Run"))
    (mdef-body md)))

; The token is the 4 little-endian bytes after the two-byte opcode FE 15 (initobj, III.4.10).
(define (initobj-token body)
  (define idx (for/first ([i (in-range (sub1 (bytes-length body)))]
                          #:when (and (= (bytes-ref body i) #xFE) (= (bytes-ref body (add1 i)) #x15)))
                i))
  (and idx (integer-bytes->integer (subbytes body (+ idx 2) (+ idx 6)) #f #f)))

; The local is always Pair, so only the initobj operand varies.
(define (lower-with-initobj type-name)
  (lower-module
   (parse-il
    (program `(.class (public) Main
                [(.method (public static) void Run () (cil managed)
                   { (.maxstack 8) (.locals init ((valuetype Pair)))
                     (ldloca.s 0) (initobj ,type-name) (ret) })])
             value-type-pair))))

(test-case "a value type extends System.ValueType through a TypeRef base"
  (define cp (lower value-type-pair))
  (define td (findf (λ (td) (equal? (tdef-name td) "Pair")) (cli-program-typedefs cp)))
  (check-equal? (car (tdef-extends td)) 'typeref)
  (define rid (cdr (tdef-extends td)))
  (define row (list-ref (cli-program-typerefs cp) (sub1 rid)))
  (check-equal? (cadr row) "System")
  (check-equal? (caddr row) "ValueType"))

(test-case "a value type cannot extend an interface"
  (check-exn #rx"Pair cannot extend interface I"
             (λ () (lower '(.class (public abstract interface auto ansi) I [])
                          '(.class (public sequential ansi sealed) Pair (.extends I) [])))))

(test-case "a value type cannot extend an unknown class"
  (check-exn #rx"Pair extends unknown class Nope"
             (λ () (lower '(.class (public sequential ansi sealed) Pair (.extends Nope) [])))))

(test-case "initobj on a value type declared in this module uses a TypeDef token"
  (define cp (lower-with-initobj 'Pair))
  (define tok (initobj-token (run-body cp)))
  (define pair-index
    (add1 (index-where (cli-program-typedefs cp) (λ (td) (equal? (tdef-name td) "Pair")))))
  (check-equal? tok (bitwise-ior #x02000000 pair-index)))

(test-case "initobj on a class name that is not in this module is rejected"
  (check-exn #rx"type operand Nope is not supported"
             (λ () (lower-with-initobj 'Nope))))
