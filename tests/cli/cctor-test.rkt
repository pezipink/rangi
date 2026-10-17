#lang racket/base
; The type initializer .cctor (II.10.5.3.1) is a static, specialname, rtspecialname method with
; no parameters and a void return. Its access defaults to private, as compilers emit it. The
; TypeDef carries no beforefieldinit bit (II.10.5.3.1, II.22.37) unless the source asks for one.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define beforefieldinit #x100000)

; A Store class holding the given methods, and a <Module> entry point that calls nothing.
(define (il-with store-methods)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) (ret) })])
     (.class (public auto ansi) Store [,@store-methods]))))

(define (store-typedef cp)
  (findf (λ (td) (equal? (tdef-name td) "Store")) (cli-program-typedefs cp)))

(define (method-named td name)
  (findf (λ (md) (equal? (mdef-name md) name)) (tdef-methods td)))

(define static-init
  '(.method (private static specialname rtspecialname) void .cctor () (cil managed)
     { (.maxstack 8) (ldc.i4.6) (ldc.i4.7) (mul) (stsfld Store value int32) (ret) }))

(define value-field '(.field (public static) int32 value))

(test-case "a .cctor is named .cctor with static, specialname and rtspecialname flags"
  (define cp (lower-module (il-with (list value-field static-init))))
  (define cctor (method-named (store-typedef cp) ".cctor"))
  (check-true (mdef? cctor))
  ; Private (0x1) | Static (0x10) | SpecialName (0x800) | RTSpecialName (0x1000)
  (check-equal? (mdef-flags cctor) #x1811))

(test-case "a .cctor keeps a public access keyword as written"
  (define cp
    (lower-module
     (il-with (list value-field
                    '(.method (public static specialname rtspecialname) void .cctor () (cil managed)
                       { (.maxstack 8) (ret) })))))
  ; Public (0x6) | Static | SpecialName | RTSpecialName
  (check-equal? (mdef-flags (method-named (store-typedef cp) ".cctor")) #x1816))

(test-case "the TypeDef of a class with a .cctor is not beforefieldinit"
  (define cp (lower-module (il-with (list value-field static-init))))
  (check-equal? (bitwise-and (tdef-flags (store-typedef cp)) beforefieldinit) 0))

(test-case "a .cctor that takes a parameter is rejected"
  (check-exn #rx"must return void and take no parameters"
             (λ () (lower-module
                    (il-with (list '(.method (private static specialname rtspecialname) void .cctor (int32) (cil managed)
                                      { (.maxstack 8) (ret) })))))))

(test-case "a .cctor that returns a value is rejected"
  (check-exn #rx"must return void and take no parameters"
             (λ () (lower-module
                    (il-with (list '(.method (private static specialname rtspecialname) int32 .cctor () (cil managed)
                                      { (.maxstack 8) (ldc.i4.1) (ret) })))))))

; The helper's <Module> main is the only entry point, so this module has no other one.
(test-case "a .cctor marked as the entry point is rejected"
  (check-exn #rx"cannot be the entry point"
             (λ () (lower-module
                    (parse-il
                     `((.assembly extern ,mscorlib-path {})
                       (.assembly donothing {})
                       (.module local.exe)
                       (.class (public auto ansi) Store
                         [(.method (private static specialname rtspecialname) void .cctor () (cil managed)
                            { (.entrypoint) (.maxstack 8) (ret) })])))))))
