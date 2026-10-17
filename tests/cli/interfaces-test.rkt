#lang racket/base
; Interfaces and implementation (II.10.1 interfaces, II.22.23 InterfaceImpl, II.22.37 TypeDef
; flags, II.22.26 MethodDef flags). An interface is an abstract class with the interface flag.
; A class lists the interfaces it implements with .implements inside its body, which lowers to
; InterfaceImpl rows.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly interface-tests {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define (parse . classes)
  (parse-il (apply program classes)))

(define base-ctor
  '(.method (public specialname rtspecialname) void .ctor () (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) }))

(define area-impl
  '(.method (public virtual newslot) int32 Area () (cil managed)
     { (.maxstack 8) (ldc.i4.4) (ret) }))

(define iarea
  '(.class (public abstract interface auto ansi) IArea
     [(.method (public virtual abstract newslot) int32 Area ())]))

(define (square-class . members)
  `(.class (public auto ansi) Square
     (.extends (mscorlib System.Object))
     [,base-ctor ,@members]))

(define (class-named m name)
  (findf (λ (c) (eq? (class-decl-name c) name)) (module-model-classes m)))

(define (typedef-named p name)
  (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs p)))

(define (rid-of p name)
  (add1 (index-of (map tdef-name (cli-program-typedefs p)) name)))

(test-case "an interface is an abstract class with the interface flag (II.22.37)"
  (define p (lower iarea (square-class area-impl '(.implements IArea))))
  ; public (0x1) | interface (0x20) | abstract (0x80)
  (check-equal? (tdef-flags (typedef-named p "IArea")) #xA1))

(test-case "the interface method is abstract, virtual, and newslot, with no body (II.22.26)"
  (define p (lower iarea (square-class area-impl '(.implements IArea))))
  (define md (findf (λ (m) (equal? (mdef-name m) "Area"))
                    (tdef-methods (typedef-named p "IArea"))))
  ; public (0x6) | virtual (0x40) | newslot (0x100) | abstract (0x400)
  (check-equal? (mdef-flags md) #x546)
  (check-false (mdef-body md)))

(test-case ".implements parses to the interface names, in source order"
  (define m (parse iarea
                   `(.class (public auto ansi) Shape
                      (.extends (mscorlib System.Object))
                      [,base-ctor ,area-impl (.implements IArea) (.implements (mscorlib System.IDisposable))])))
  (check-equal? (class-decl-implements (class-named m 'Shape))
                '(IArea (mscorlib System.IDisposable))))

(test-case "a class with no .implements has an empty list"
  (define m (parse iarea (square-class area-impl)))
  (check-equal? (class-decl-implements (class-named m 'Square)) '()))

(test-case "a same-module .implements lowers to an InterfaceImpl row with a TypeDef interface"
  (define p (lower iarea
                   (square-class area-impl '(.implements IArea))))
  (define rows (cli-program-interfaceimpls p))
  (check-equal? (length rows) 1)
  (check-equal? (interfaceimpl-class (car rows)) (rid-of p "Square"))
  (check-equal? (interfaceimpl-iface (car rows)) (cons 'typedef (rid-of p "IArea"))))

(test-case "a class with no .implements has no InterfaceImpl rows"
  (define p (lower (square-class area-impl)))
  (check-equal? (cli-program-interfaceimpls p) '()))

(test-case "an external .implements lowers to a TypeRef interface and is not checked"
  (define p (lower `(.class (public auto ansi) Disp
                      (.extends (mscorlib System.Object))
                      [,base-ctor (.implements (mscorlib System.IDisposable))])))
  (define rows (cli-program-interfaceimpls p))
  (check-equal? (length rows) 1)
  (check-equal? (car (interfaceimpl-iface (car rows))) 'typeref))

(test-case "a method inherited from a same-module base satisfies the interface"
  (define p (lower iarea
                   `(.class (public auto ansi) Base
                      (.extends (mscorlib System.Object))
                      [,base-ctor ,area-impl])
                   `(.class (public auto ansi) Derived
                      (.extends Base)
                      [(.implements IArea)])))
  (check-equal? (length (cli-program-interfaceimpls p)) 1))

(test-case "a method inherited from System.Object satisfies an Object virtual"
  (define p (lower `(.class (public abstract interface auto ansi) IStr
                      [(.method (public virtual abstract newslot) string ToString ())])
                   `(.class (public auto ansi) Plain
                      [(.implements IStr)])))
  (check-equal? (length (cli-program-interfaceimpls p)) 1))

(test-case "an interface must be abstract"
  (check-exn #rx"interface I must be abstract"
             (λ () (lower '(.class (public interface auto ansi) I
                             [(.method (public virtual abstract newslot) int32 Area ())])))))

(test-case "an interface cannot implement another interface"
  (check-exn #rx"interface J cannot have .implements"
             (λ () (lower iarea
                          '(.class (public abstract interface auto ansi) J
                             [(.method (public virtual abstract newslot) int32 Area ())
                              (.implements IArea)])))))

(test-case "an interface method must be abstract and virtual"
  (check-exn #rx"interface method I.Area must be abstract, virtual"
             (λ () (lower '(.class (public abstract interface auto ansi) I
                             [(.method (public virtual newslot) int32 Area () (cil managed)
                                { (.maxstack 8) (ldc.i4.1) (ret) })])))))

(test-case "an abstract interface method cannot have a body"
  (check-exn #rx"abstract method Area in IArea cannot have a body"
             (λ () (parse '(.class (public abstract interface auto ansi) IArea
                             [(.method (public virtual abstract newslot) int32 Area () (cil managed)
                                { (.maxstack 8) (ldc.i4.1) (ret) })])))))

(test-case "a class that implements an interface must provide each interface method"
  (check-exn #rx"Square does not implement IArea.Area"
             (λ () (lower iarea (square-class '(.implements IArea))))))

(test-case "a non-virtual method does not satisfy an interface method"
  (check-exn #rx"Square does not implement IArea.Area"
             (λ () (lower iarea
                          (square-class '(.method (public) int32 Area () (cil managed)
                                           { (.maxstack 8) (ldc.i4.4) (ret) })
                                        '(.implements IArea))))))

(test-case "a method with a different signature does not satisfy an interface method"
  (check-exn #rx"Square does not implement IArea.Area"
             (λ () (lower iarea
                          (square-class '(.method (public virtual newslot) int64 Area () (cil managed)
                                           { (.maxstack 8) (ldc.i8 4) (ret) })
                                        '(.implements IArea))))))

(test-case ".implements of a class that is not an interface is rejected"
  (check-exn #rx"Bad implements Other, which is not an interface"
             (λ () (lower `(.class (public auto ansi) Other
                             (.extends (mscorlib System.Object))
                             [,base-ctor])
                          `(.class (public auto ansi) Bad
                             (.extends (mscorlib System.Object))
                             [,base-ctor (.implements Other)])))))

(test-case ".implements of an unknown name is rejected"
  (check-exn #rx"Bad implements unknown interface Nope"
             (λ () (lower `(.class (public auto ansi) Bad
                             (.extends (mscorlib System.Object))
                             [,base-ctor (.implements Nope)])))))

(test-case "a duplicate .implements is rejected"
  (check-exn #rx"duplicate .implements IArea in Square"
             (λ () (parse iarea (square-class area-impl '(.implements IArea) '(.implements IArea))))))

(test-case ".implements is not allowed in <Module>"
  (check-exn #rx"\\.implements is not allowed in <Module>"
             (λ () (parse-il `((.assembly extern ,mscorlib-path {})
                               (.assembly interface-tests {})
                               (.module local.exe)
                               (.class (private auto ansi) <Module>
                                 [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })
                                  (.implements IArea)]))))))

(test-case "a malformed .implements is rejected"
  (check-exn #rx"malformed .implements in Bad"
             (λ () (parse `(.class (public auto ansi) Bad (.extends (mscorlib System.Object))
                             [,base-ctor (.implements 5)])))))
