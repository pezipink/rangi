#lang racket/base
; Instance methods take this as argument zero (II.22.26, II.23.2.1), so ldarg indices count it.
; newobj names a same-module .ctor, which must be an instance method. A call to an instance
; method pops the receiver as well as its arguments (III.3.19, III.4.19).
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (module-with main-flags main-body store-methods)
  (lower-module
   (parse-il
    `((.assembly extern ,mscorlib-path {})
      (.assembly donothing {})
      (.module local.exe)
      (.class (private auto ansi) <Module>
        [(.method ,main-flags void main () (cil managed)
           { (.entrypoint) (.maxstack 8) ,@main-body (ret) })])
      (.class (public auto ansi) Store
        [,@store-methods])))))

(define bump
  '(.method (public) void Bump (int32) (cil managed)
     { (.maxstack 8) (ldarg.0) (ldarg.1) (pop) (pop) (ret) }))

(define ctor
  '(.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) }))

(test-case "an instance method's ldarg.1 is its first parameter, since this is argument zero"
  (check-not-exn
   (λ () (module-with '(public static) '((ldc.i4.1) (newobj (Store) (int32)) (pop))
                      (list ctor bump)))))

(test-case "ldarg.2 is out of range in an instance method with one parameter"
  (check-exn #rx"index 2 is out of range"
             (λ () (module-with '(public static) '((ldc.i4.1) (pop))
                                (list
                                 '(.method (public) void Bump (int32) (cil managed)
                                    { (.maxstack 8) (ldarg 2) (pop) (ret) })
                                 ctor)))))

(test-case "a static method's ldarg.1 with one parameter is out of range, as before"
  (check-exn #rx"index 1 is out of range"
             (λ () (module-with '(public static) '()
                                (list
                                 '(.method (public static) void S (int32) (cil managed)
                                    { (.maxstack 8) (ldarg 1) (pop) (ret) })
                                 ctor)))))

(test-case "an instance entry point is rejected"
  (check-exn #rx"entry point .*must be static"
             (λ () (module-with '(public) '() (list ctor bump)))))

(test-case "newobj of a class with no matching .ctor is rejected"
  (check-exn #rx"no \\.ctor in Store"
             (λ () (module-with '(public static) '((ldc.i4.1) (newobj (Store) (int32)) (pop))
                                (list bump)))))

(test-case "newobj of a static .ctor is rejected"
  (check-exn #rx"must be an instance method"
             (λ () (module-with '(public static) '((ldc.i4.1) (newobj (Store) (int32)) (pop))
                                (list
                                 '(.method (public static specialname rtspecialname) void .ctor (int32) (cil managed)
                                    { (.maxstack 8) (ret) }))))))

(test-case "a call to an instance method with no receiver on the stack underflows"
  (check-exn #rx"stack underflow"
             (λ () (module-with '(public static) '((ldc.i4.1) (call void (Store) Bump (int32)))
                                (list ctor bump)))))

(test-case "newobj, callvirt, and a non-virtual call to an instance method lower together"
  (check-not-exn
   (λ () (module-with '(public static)
                      '((ldc.i4.1) (newobj (Store) (int32)) (dup) (ldc.i4.4)
                        (call void (Store) Bump (int32))
                        (ldc.i4.2)
                        (callvirt void (Store) Bump (int32)))
                      (list ctor bump)))))
