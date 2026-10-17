#lang racket/base
; Virtual methods and .override (II.22.26 MethodDef flags, II.22.27 MethodImpl, II.10.3 virtual
; dispatch). Flags are checked on the lowered MethodDef rows, the MethodImpl row is checked on
; the lowered program, and the error cases are checked on the module that fails to lower.
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (lower-classes . classes)
  (lower-module
   (parse-il
    `((.assembly extern ,mscorlib-path {})
      (.assembly virtual-tests {})
      (.module local.exe)
      (.class (private auto ansi) <Module>
        [(.method (public static) void main () (cil managed)
           { (.entrypoint) (.maxstack 8) (ret) })])
      ,@classes))))

(define base-ctor
  '(.method (public specialname rtspecialname) void .ctor () (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) }))

(define derived-ctor
  '(.method (public specialname rtspecialname) void .ctor () (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (Base) .ctor ()) (ret) }))

(define base-class
  `(.class (public auto ansi) Base
     (.extends (mscorlib System.Object))
     [,base-ctor
      (.method (public virtual newslot) int32 Get () (cil managed)
        { (.maxstack 8) (ldc.i4.1) (ret) })]))

(define derived-class
  `(.class (public auto ansi) Derived
     (.extends Base)
     [,derived-ctor
      (.method (public virtual) int32 Get () (cil managed)
        { (.maxstack 8) (ldc.i4.2) (ret) })
      (.override Base::Get int32 ())]))

(define (typedef prog name)
  (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs prog)))

(define (method prog class-name method-name)
  (findf (λ (md) (equal? (mdef-name md) method-name))
         (tdef-methods (typedef prog class-name))))

(test-case "virtual, newslot, final, and abstract map to MethodDef flags (II.22.26)"
  (define prog
    (lower-classes
     base-class
     derived-class
     `(.class (public abstract auto ansi) Shape
        [,base-ctor
         (.method (public virtual abstract) int32 Area ())
         (.method (public virtual final newslot) int32 Sides () (cil managed)
           { (.maxstack 8) (ldc.i4.4) (ret) })])))
  ; public (0x6) | virtual (0x40) | newslot (0x100)
  (check-equal? (mdef-flags (method prog "Base" "Get")) #x146)
  ; an override does not set newslot, so it reuses the base slot
  (check-equal? (mdef-flags (method prog "Derived" "Get")) #x46)
  ; public | virtual | final (0x20) | newslot
  (check-equal? (mdef-flags (method prog "Shape" "Sides")) #x166))

(test-case "an abstract method lowers with no body (II.22.26, RVA 0)"
  (define prog
    (lower-classes
     `(.class (public abstract auto ansi) Shape
        [,base-ctor
         (.method (public virtual abstract) int32 Area ())])))
  (define area (method prog "Shape" "Area"))
  ; public | virtual | abstract (0x400)
  (check-equal? (mdef-flags area) #x446)
  (check-false (mdef-body area)))

(test-case "a .override lowers to one MethodImpl row (II.22.27)"
  (define prog (lower-classes base-class derived-class))
  ; <Module> holds main in the generated Program class: Program=2, Base=3, Derived=4.
  ; Methods: main=1, Base .ctor=2, Base.Get=3, Derived .ctor=4, Derived.Get=5.
  (define rows (cli-program-methodimpls prog))
  (check-equal? (length rows) 1)
  (define row (car rows))
  (check-equal? (methodimpl-class row) 4)
  (check-equal? (methodimpl-body row) '(methoddef . 5))
  (check-equal? (methodimpl-decl row) '(methoddef . 3)))

(test-case "a program with no .override has no MethodImpl rows"
  (check-equal? (cli-program-methodimpls (lower-classes base-class)) '()))

(test-case ".override naming a base method that does not exist is an error"
  (check-exn #rx"no method Nope with this signature in base class Base"
             (λ ()
               (lower-classes
                base-class
                `(.class (public auto ansi) Derived
                   (.extends Base)
                   [,derived-ctor
                    (.method (public virtual) int32 Nope () (cil managed)
                      { (.maxstack 8) (ldc.i4.2) (ret) })
                    (.override Base::Nope int32 ())])))))

(test-case ".override with no body method in the derived class is an error"
  (check-exn #rx"Derived has no method Get to override Base::Get"
             (λ ()
               (lower-classes
                base-class
                `(.class (public auto ansi) Derived
                   (.extends Base)
                   [,derived-ctor
                    (.override Base::Get int32 ())])))))

(test-case ".override of a base that is not an ancestor is an error"
  (check-exn #rx"Other is not a base class of Derived"
             (λ ()
               (lower-classes
                base-class
                `(.class (public auto ansi) Other
                   (.extends (mscorlib System.Object))
                   [,base-ctor
                    (.method (public virtual newslot) int32 Get () (cil managed)
                      { (.maxstack 8) (ldc.i4.1) (ret) })])
                `(.class (public auto ansi) Derived
                   (.extends Base)
                   [,derived-ctor
                    (.method (public virtual) int32 Get () (cil managed)
                      { (.maxstack 8) (ldc.i4.2) (ret) })
                    (.override Other::Get int32 ())])))))

(test-case "abstract without virtual is an error"
  (check-exn #rx"abstract method Shape.Area must be virtual"
             (λ ()
               (lower-classes
                `(.class (public abstract auto ansi) Shape
                   [,base-ctor
                    (.method (public abstract) int32 Area ())])))))

(test-case "abstract method in a non-abstract class is an error"
  (check-exn #rx"abstract method Area in non-abstract class Shape"
             (λ ()
               (lower-classes
                `(.class (public auto ansi) Shape
                   [,base-ctor
                    (.method (public virtual abstract) int32 Area ())])))))

(test-case "a body-less method that is not abstract is a parse error"
  (check-exn #rx"method Get in Base has no body; only abstract methods may omit it"
             (λ ()
               (lower-classes
                `(.class (public auto ansi) Base
                   [,base-ctor
                    (.method (public virtual) int32 Get ())])))))

(test-case "newslot without virtual is an error"
  (check-exn #rx"newslot and final on Base.Get need virtual"
             (λ ()
               (lower-classes
                `(.class (public auto ansi) Base
                   [,base-ctor
                    (.method (public newslot) int32 Get () (cil managed)
                      { (.maxstack 8) (ldc.i4.1) (ret) })])))))
