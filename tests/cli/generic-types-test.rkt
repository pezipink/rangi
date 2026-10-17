#lang racket/base
; Generic type definitions: the arity-suffixed TypeDef name (II.10.7), GenericParam rows owned by
; the TypeDef with GenericParamAttributes (II.22.20, II.23.1.7), and GenericParamConstraint rows
; (II.22.21) whose target is a TypeDefOrRef (II.24.2.6).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly generic-type-tests {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define base-ctor
  '(.method (public specialname rtspecialname) void .ctor () (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) }))

(define iarea
  '(.class (public abstract interface auto ansi) IArea
     [(.method (public virtual abstract newslot) int32 Area ())]))

(define box
  `(.class (public auto ansi) Box (.typarams (T class .ctor) (U (class IArea)) (V valuetype))
     (.extends (mscorlib System.Object))
     [,base-ctor]))

(define (typedef-named p name)
  (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs p)))

(define (rid-of p name)
  (add1 (index-of (map tdef-name (cli-program-typedefs p)) name)))

(define (params-of p owner-rid)
  (filter (λ (gp) (equal? (cadddr gp) (cons 'typedef owner-rid)))
          (cli-program-genericparams p)))

(test-case "a generic TypeDef name carries its arity (II.10.7)"
  (define p (lower iarea box))
  (check-true (and (typedef-named p "Box`3") #t) "name is Box`3")
  (check-false (typedef-named p "Box") "the bare name is not used")
  (check-equal? (tdef-name (typedef-named p "IArea")) "IArea"))

(test-case "GenericParam rows are owned by the TypeDef with flags and names (II.22.20, II.23.1.7)"
  (define p (lower iarea box))
  (define owner (rid-of p "Box`3"))
  (define gps (params-of p owner))
  (check-equal? (map cadr gps)
                (list #x0014 #x0000 #x0008))
  (check-equal? (map caddr gps) (list "T" "U" "V")))

(test-case "GenericParam numbers are declaration order (II.22.20)"
  (define p (lower iarea box))
  (define owner (rid-of p "Box`3"))
  (check-equal? (map car (params-of p owner)) '(0 1 2)))

(test-case "GenericParamConstraint rows target the TypeDefOrRef of the constraint (II.22.21)"
  (define p (lower iarea box))
  (define owner (rid-of p "Box`3"))
  (define gps (params-of p owner))
  (check-equal? (list-ref (list-ref gps 0) 4) '())
  (check-equal? (list-ref (list-ref gps 1) 4) (list (cons 'typedef (rid-of p "IArea"))))
  (check-equal? (list-ref (list-ref gps 2) 4) '()))

(test-case "a class with no type parameters keeps its plain name and has no GenericParam rows"
  (define p (lower iarea
                   `(.class (public auto ansi) Plain
                      (.extends (mscorlib System.Object))
                      [,base-ctor])))
  (check-true (and (typedef-named p "Plain") #t))
  (check-equal? (params-of p (rid-of p "Plain")) '()))

(test-case "a generic class with the class and valuetype specials together is rejected"
  (check-exn #rx"class and valuetype"
             (λ ()
               (lower `(.class (public auto ansi) Both (.typarams (T class valuetype))
                         (.extends (mscorlib System.Object))
                         [,base-ctor])))))

(define gen-a
  `(.class (public auto ansi) Gen (.typarams A)
     (.extends (mscorlib System.Object))
     [,base-ctor]))

(test-case "a generic class used without type arguments as a constraint is rejected"
  (check-exn #rx"without type arguments"
             (λ ()
               (lower gen-a
                      `(.class (public auto ansi) Bad (.typarams (T (class Gen)))
                         (.extends (mscorlib System.Object))
                         [,base-ctor])))))

(test-case "a generic instance with the wrong number of type arguments is rejected"
  (check-exn #rx"takes 3 type arguments, got 1"
             (λ ()
               (lower iarea box
                      `(.class (public auto ansi) User
                         (.extends (mscorlib System.Object))
                         [,base-ctor
                          (.method (public static) void Take ((class Box (int32))) (cil managed)
                            { (ret) })])))))
