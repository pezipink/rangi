#lang racket/base
; Same-module calls lower to MethodDef tokens (II.22.26). Forward calls and recursion resolve
; because the MethodDef index is built before any body is lowered. Mismatched signatures,
; callvirt on a local method, and unknown classes are rejected (II.23.2.1).
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define (program-with . body-forms)
  (parse-il
   `((.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) ,@body-forms (ret) })
        (.method (public static) int32 f (int32) (cil managed)
          { (.maxstack 8) (ldarg.0) (ret) })]))))

(test-case "a forward call and a recursive call lower without error"
  (check-not-exn
   (λ ()
     (lower-module
      (parse-il
       '((.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
         (.assembly donothing {})
         (.module local.exe)
         (.class (private auto ansi) <Module>
           [(.method (public static) void main () (cil managed)
              { (.entrypoint) (.maxstack 8)
                (ldc.i4.3) (call int32 (Program) fact (int32)) (pop) (ret) })
            (.method (public static) int32 fact (int32) (cil managed)
              { (.maxstack 8)
                (ldarg.0) (ldc.i4.1) (ble base)
                (ldarg.0) (ldarg.0) (ldc.i4.1) sub (call int32 (Program) fact (int32)) mul (ret)
                base: (ldc.i4.1) (ret) })])))))))

(test-case "callvirt on a same-module method is rejected"
  (check-exn #rx"callvirt to same-module method f is not supported"
             (λ () (lower-module (program-with '(ldc.i4.1) '(callvirt int32 (Program) f (int32)) '(pop))))))

(test-case "a call whose signature does not match the MethodDef signature is rejected"
  (check-exn #rx"no method f in Program"
             (λ () (lower-module (program-with '(ldc.i4.1) '(call int32 (Program) f (int64)) '(pop))))))

(test-case "a call whose return type does not match the MethodDef signature is rejected"
  (check-exn #rx"no method f in Program"
             (λ () (lower-module (program-with '(ldc.i4.1) '(call void (Program) f (int32)))))))

(test-case "a call to an unknown class is rejected"
  (check-exn #rx"no method f in Nope"
             (λ () (lower-module (program-with '(ldc.i4.1) '(call int32 (Nope) f (int32)) '(pop))))))
