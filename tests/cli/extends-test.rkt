#lang racket/base
; A class may name its base with (.extends T). A same-module base is a bare class name, and an
; external base is (asm ty). Bases must exist, must be classes rather than interfaces or <Module>,
; and must not form a cycle (II.22.37).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly extends-test {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define (base-of p name)
  (tdef-extends (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs p))))

(define base-class '(.class (public auto ansi) Base (.extends (mscorlib System.Object)) []))
(define derived-class '(.class (public auto ansi) Derived (.extends Base) []))

(test-case "a class with no .extends has no explicit base in the model"
  (define m (parse-il (program '(.class (public auto ansi) Plain []))))
  (check-false (class-decl-extends (findf (λ (c) (eq? (class-decl-name c) 'Plain))
                                          (module-model-classes m)))))

(test-case ".typarams and .extends may appear in either order before the body"
  (define m (parse-il (program '(.class (public auto ansi) G (.typarams (T)) (.extends Base) []) base-class)))
  (define g (findf (λ (c) (eq? (class-decl-name c) 'G)) (module-model-classes m)))
  (check-equal? (class-decl-extends g) 'Base)
  (check-equal? (length (class-decl-gparams g)) 1))

(test-case "a same-module base lowers to a TypeDef tag, and a base declared later also resolves"
  (define p (lower derived-class base-class))
  ; <Module> (row 1) and the Program class that takes its method (row 2) come before Derived
  (check-equal? (base-of p "Derived") (cons 'typedef 4))
  (check-equal? (car (base-of p "Base")) 'typeref))

(test-case "a class with no .extends derives from System.Object, a TypeRef"
  (define p (lower '(.class (public auto ansi) Plain [])))
  (check-equal? (car (base-of p "Plain")) 'typeref))

(test-case "a duplicate .extends is rejected"
  (check-exn #rx"duplicate \\.extends in class D"
             (λ () (parse-il (program '(.class (public) D (.extends Base) (.extends Base) []))))))

(test-case "an unknown clause in a class header is rejected"
  (check-exn #rx"unsupported class clause \\(\\.foo\\) in C"
             (λ () (parse-il (program '(.class (public) C (.foo) []))))))

(test-case "a base that is not a class in this module is rejected"
  (check-exn #rx"D extends unknown class Nope"
             (λ () (lower '(.class (public) D (.extends Nope) [])))))

(test-case "a class cannot extend itself"
  (check-exn #rx"cyclic inheritance involving A"
             (λ () (lower '(.class (public) A (.extends A) [])))))

(test-case "a longer inheritance cycle is rejected"
  (check-exn #rx"cyclic inheritance"
             (λ () (lower '(.class (public) A (.extends B) [])
                          '(.class (public) B (.extends C) [])
                          '(.class (public) C (.extends A) [])))))

(test-case "a class cannot extend an interface"
  (check-exn #rx"D cannot extend interface I"
             (λ () (lower '(.class (public abstract interface auto ansi) I [])
                          '(.class (public) D (.extends I) [])))))

(test-case "an interface cannot have a base"
  (check-exn #rx"I cannot have a base class"
             (λ () (lower '(.class (public abstract interface auto ansi) I (.extends Base) [])
                          base-class))))

(test-case "a class cannot extend <Module>"
  (check-exn #rx"D cannot extend <Module>"
             (λ () (lower '(.class (public) D (.extends <Module>) [])))))

(test-case "<Module> cannot have a base"
  (check-exn #rx"<Module> cannot have a base class"
             (λ () (lower-module (parse-il `((.assembly extern ,mscorlib-path {})
                                             (.assembly extends-test {})
                                             (.module local.exe)
                                             (.class (private auto ansi) <Module> (.extends Base)
                                               [(.method (public static) void main () (cil managed)
                                                  { (.entrypoint) (.maxstack 8) (ret) })])
                                             ,base-class))))))

(test-case "an external base must be (assembly type)"
  (check-exn #rx"expected \\(assembly type\\)"
             (λ () (lower '(.class (public) D (.extends 5) [])))))
