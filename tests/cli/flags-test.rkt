#lang racket/base
; FieldAttributes and ParamAttributes values (ECMA-335 II.23.1.5, II.23.1.13). The expected
; integers are written out from the spec table, not read back from the module.
(require rackunit
         "../../src/cli/flags.rkt")

(test-case "FieldAccessMask values (II.23.1.5)"
  (check-equal? fa-privatescope #x0000)
  (check-equal? fa-private #x0001)
  (check-equal? fa-famandassem #x0002)
  (check-equal? fa-assembly #x0003)
  (check-equal? fa-family #x0004)
  (check-equal? fa-famorassem #x0005)
  (check-equal? fa-public #x0006)
  (check-equal? fa-access-mask #x0007))

(test-case "FieldAttributes field bits (II.23.1.5)"
  (check-equal? fa-static #x0010)
  (check-equal? fa-initonly #x0020)
  (check-equal? fa-literal #x0040)
  (check-equal? fa-notserialized #x0080)
  (check-equal? fa-hasfieldrva #x0100)
  (check-equal? fa-specialname #x0200)
  (check-equal? fa-rtspecialname #x0400)
  (check-equal? fa-hasfieldmarshal #x1000)
  (check-equal? fa-pinvokeimpl #x2000)
  (check-equal? fa-hasdefault #x8000)
  (check-equal? fa-reserved-mask #x9500))

(test-case "ParamAttributes values (II.23.1.13)"
  (check-equal? pa-in #x0001)
  (check-equal? pa-out #x0002)
  (check-equal? pa-lcid #x0004)
  (check-equal? pa-retval #x0008)
  (check-equal? pa-optional #x0010)
  (check-equal? pa-hasdefault #x1000)
  (check-equal? pa-hasfieldmarshal #x2000)
  (check-equal? pa-reserved3 #x4000)
  (check-equal? pa-reserved4 #x8000)
  (check-equal? pa-reserved-mask #xF000))

(test-case "field keyword list: (public static initonly) is 0x36"
  (check-equal? (field-attributes-flags '(public static initonly)) #x36))

(test-case "each field access keyword maps to its access value"
  (check-equal? (field-attributes-flags '(privatescope)) #x0000)
  (check-equal? (field-attributes-flags '(compilercontrolled)) #x0000)
  (check-equal? (field-attributes-flags '(private)) #x0001)
  (check-equal? (field-attributes-flags '(famandassem)) #x0002)
  (check-equal? (field-attributes-flags '(assembly)) #x0003)
  (check-equal? (field-attributes-flags '(family)) #x0004)
  (check-equal? (field-attributes-flags '(famorassem)) #x0005)
  (check-equal? (field-attributes-flags '(public)) #x0006))

(test-case "each field non-access keyword maps to its bit"
  (check-equal? (field-attributes-flags '(static)) #x0010)
  (check-equal? (field-attributes-flags '(initonly)) #x0020)
  (check-equal? (field-attributes-flags '(literal)) #x0040)
  (check-equal? (field-attributes-flags '(notserialized)) #x0080)
  (check-equal? (field-attributes-flags '(specialname)) #x0200)
  (check-equal? (field-attributes-flags '(rtspecialname)) #x0400))

(test-case "no field keywords gives 0 (PrivateScope)"
  (check-equal? (field-attributes-flags '()) 0))

(test-case "keyword order does not change the field flags"
  (check-equal? (field-attributes-flags '(initonly static public))
                (field-attributes-flags '(public static initonly))))

(test-case "two field access keywords are rejected"
  (check-exn exn:fail? (λ () (field-attributes-flags '(public private))))
  (check-exn exn:fail? (λ () (field-attributes-flags '(privatescope compilercontrolled)))))

(test-case "method-only or unknown keywords are rejected for fields"
  (check-exn exn:fail? (λ () (field-attributes-flags '(virtual))))
  (check-exn exn:fail? (λ () (field-attributes-flags '(in)))))

(test-case "parameter keywords map to their bits"
  (check-equal? (param-attributes-flags '(in)) #x0001)
  (check-equal? (param-attributes-flags '(out)) #x0002)
  (check-equal? (param-attributes-flags '(lcid)) #x0004)
  (check-equal? (param-attributes-flags '(retval)) #x0008)
  (check-equal? (param-attributes-flags '(optional)) #x0010)
  (check-equal? (param-attributes-flags '(opt)) #x0010))

(test-case "parameter keyword lists combine and an empty list is 0"
  (check-equal? (param-attributes-flags '(in out optional)) #x0013)
  (check-equal? (param-attributes-flags '(out in)) #x0003)
  (check-equal? (param-attributes-flags '()) 0))

(test-case "unknown parameter keywords are rejected"
  (check-exn exn:fail? (λ () (param-attributes-flags '(static))))
  (check-exn exn:fail? (λ () (param-attributes-flags '(public)))))
