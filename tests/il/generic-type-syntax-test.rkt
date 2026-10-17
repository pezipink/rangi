#lang racket/base
; Syntax of generic class type parameters and their constraints (II.10.1.7, II.22.20, II.22.21).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt")

(define (program cls)
  `((.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
    (.assembly generic-syntax {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,cls))

(define (box-class tp)
  `(.class (public auto ansi) Box ,tp
     (.extends (mscorlib System.Object))
     [(.method (public specialname rtspecialname) void .ctor () (cil managed)
        { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) })]))

(define (box-gparams tp)
  (class-decl-gparams
   (findf (λ (c) (eq? (class-decl-name c) 'Box))
          (module-model-classes (parse-il (program (box-class tp)))))))

(test-case "specials and constraints parse in source order"
  (check-equal? (box-gparams '(.typarams (T class .ctor (class IArea)) (U valuetype) (V (class Foo (int32 !0)))))
                (list (generic-param 'T '(class .ctor) '((class IArea)))
                      (generic-param 'U '(valuetype) '())
                      (generic-param 'V '() '((class Foo (int32 !0)))))))

(test-case "a bare parameter has no specials and no constraints"
  (check-equal? (box-gparams '(.typarams T))
                (list (generic-param 'T '() '()))))

(test-case "a constraint naming an undeclared class variable is rejected"
  (check-exn #rx"out of range"
             (λ () (box-gparams '(.typarams (T (class Foo (!2))))))))

(test-case "a bare class variable constraint naming an undeclared parameter is rejected"
  (check-exn #rx"out of range"
             (λ () (box-gparams '(.typarams (T !1))))))

(test-case "an unknown special keyword is rejected"
  (check-exn #rx"invalid constraint"
             (λ () (box-gparams '(.typarams (T frob))))))

(test-case "a repeated special is rejected"
  (check-exn #rx"duplicate special constraint"
             (λ () (box-gparams '(.typarams (T class class))))))

; A module with the given classes, for constraints that name classes of this module.
(define (module-with . classes)
  `((.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
    (.assembly generic-syntax {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define plain-class
  `(.class (public auto ansi) Plain (.extends (mscorlib System.Object)) []))

(define (gen-class tp)
  `(.class (public auto ansi) Gen ,tp (.extends (mscorlib System.Object)) []))

(define (holder-with-method-typarams tp)
  `(.class (public auto ansi) Holder (.extends (mscorlib System.Object))
     [(.method (public static) void M ,tp () (cil managed) { (.maxstack 8) (ret) })]))

(test-case "a constraint with type arguments on a non-generic local class is a parse error"
  (check-exn #rx"names non-generic class Plain"
             (λ () (parse-il (module-with plain-class
                                          (box-class '(.typarams (T (class Plain (int32)))))))))
  (check-exn #rx"names non-generic class Plain"
             (λ () (parse-il (module-with plain-class
                                          (holder-with-method-typarams '(.typarams (T (class Plain (int32))))))))))

(test-case "a constraint without type arguments on a generic local class is a parse error"
  (check-exn #rx"takes 1 type argument"
             (λ () (parse-il (module-with (gen-class '(.typarams A))
                                          (box-class '(.typarams (T (class Gen)))))))))

(test-case "a constraint with the wrong number of type arguments is a parse error"
  (check-exn #rx"gives 2 type argument\\(s\\) to Gen, which takes 1"
             (λ () (parse-il (module-with (gen-class '(.typarams A))
                                          (box-class '(.typarams (T (class Gen (int32 int32))))))))))

(test-case "valid constraints on local classes parse"
  (check-not-exn
   (λ () (parse-il (module-with plain-class
                                (gen-class '(.typarams A))
                                (box-class '(.typarams (T (class Plain)) (U (class Gen (int32)))))
                                (holder-with-method-typarams '(.typarams (V (class Plain)))))))))
