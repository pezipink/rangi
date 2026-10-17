#lang racket/base
; Token operands for the opcodes that take a type, field, or method. A type operand names a
; TypeRef (II.22.38), an unsupported type is rejected, and a field operand must match the field's
; kind (static or instance). constrained. must precede callvirt (III.2.1). calli names its call
; site in a StandAloneSig (II.22.36).
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; A module whose entry point runs body. Members declared on <Module> move to the generated
; Program class (see parse-il), so the helpers live in Helpers and Store instead.
(define (lower-with-body body)
  (lower-module
   (parse-il
    `((.assembly extern ,mscorlib-path {})
      (.assembly donothing {})
      (.module local.exe)
      (.class (private auto ansi) <Module>
        [(.method (public static) void main () (cil managed)
           { (.entrypoint) (.maxstack 8) ,@body (ret) })])
      (.class (public auto ansi) Helpers
        [(.field (public static) int32 counter)
         (.method (public static) void S () (cil managed)
           { (.maxstack 8) (ret) })])
      (.class (public auto ansi) Store
        [(.field (public) int32 weight)])))))

(test-case "box and unbox.any with a primitive type lower"
  (check-not-exn
   (λ () (lower-with-body '((ldc.i4.1) (box int32) (unbox.any int32) (pop))))))

(test-case "a void type operand is rejected"
  (check-exn #rx"type operand void is not supported"
             (λ () (lower-with-body '((ldtoken void) (pop))))))

(test-case "a type-operand instruction with no operand is malformed"
  (check-exn #rx"malformed IL instruction"
             (λ () (lower-with-body '((box))))))

(test-case "ldflda on a static field is rejected"
  (check-exn #rx"static field; ldflda needs an instance field"
             (λ () (lower-with-body '((ldflda Helpers counter int32) (pop))))))

(test-case "ldsflda on an instance field is rejected"
  (check-exn #rx"instance field; ldsflda needs a static field"
             (λ () (lower-with-body '((ldsflda Store weight int32) (pop))))))

(test-case "ldftn to a method that does not exist is rejected"
  (check-exn #rx"no method Missing in <Module>"
             (λ () (lower-with-body '((ldftn void (<Module>) Missing ()) (pop))))))

(test-case "a function pointer from ldftn can be called with calli"
  (check-not-exn
   (λ () (lower-with-body '((ldftn void (Helpers) S ()) (calli void ()))))))

(test-case "constrained. must be followed by callvirt"
  (check-exn #rx"prefix constrained. cannot precede pop"
             (λ () (lower-with-body '((ldc.i4.1) (box int32) (constrained. int32) (pop))))))

(test-case "a method type variable operand is range-checked against the method's arity"
  (check-exn #rx"type variable !!0 out of range \\(0 declared\\)"
             (λ () (lower-with-body '((box !!0) (pop))))))

(test-case "constrained. on a method type variable is accepted in a generic method"
  (check-not-exn
   (λ ()
     (lower-module
      (parse-il
       `((.assembly extern ,mscorlib-path {})
         (.assembly local {})
         (.module local.exe)
         (.class (private auto ansi) <Module>
           [(.method (public static) void main () (cil managed)
              { (.entrypoint) (.maxstack 8) (ret) })
            (.method (public static) int32 Show (.typarams (T)) (!!0) (cil managed)
              { (.maxstack 8) (ldarga.s 0) (constrained. !!0)
                (callvirt string (mscorlib System.Object) ToString ()) (pop) (ldc.i4.0) (ret) })])))))))

(test-case "constrained. before callvirt on a managed pointer is accepted"
  (check-not-exn
   (λ () (lower-with-body
          '((.locals init (int32))
            (ldloca.s 0)
            (constrained. int32)
            (callvirt string (mscorlib System.Object) ToString ())
            (pop))))))
