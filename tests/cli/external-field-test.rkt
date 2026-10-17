#lang racket/base
; An instance field of an external type is a MemberRef whose parent is the external TypeRef and
; whose signature is a FieldSig, 0x06 then the field type (II.22.25, II.23.2.4). Accesses to the
; same field intern to one MemberRef row, so ldfld and stfld share a token.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; System.Runtime.Remoting.Messaging.Header is public in mscorlib 4.7.1. Its public instance fields
; are Name (string), Value (object), and MustUnderstand (boolean). Its public .ctor takes
; (string, object).
(define (module-with main-body)
  (lower-module
   (parse-il
    `((.assembly extern ,mscorlib-path {})
      (.assembly donothing {})
      (.module local.exe)
      (.class (private auto ansi) <Module>
        [(.method (public static) void main () (cil managed)
           { (.entrypoint) (.maxstack 8) ,@main-body (ret) })])))))

(define (memberref-named cp name)
  (filter (λ (e) (equal? (cadr e) name)) (cli-program-memberrefs cp)))

(define header-access
  '((ldstr "a")
    (ldnull)
    (newobj (mscorlib System.Runtime.Remoting.Messaging.Header) (string object))
    (dup)
    (ldstr "b")
    (stfld (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
    (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
    (pop)))

(test-case "ldfld and stfld on an external instance field share one MemberRef with a string FieldSig"
  (define cp (module-with header-access))
  (define refs (memberref-named cp "Name"))
  (check-equal? (length refs) 1)
  (check-equal? (caddr (car refs)) (bytes #x06 #x0e)))

(test-case "the MemberRef parent of an external instance field is the external TypeRef"
  (define cp (module-with header-access))
  (define parent (car (car (memberref-named cp "Name"))))
  (check-equal? (car parent) 'typeref)
  (define tr (list-ref (cli-program-typerefs cp) (sub1 (cdr parent))))
  (check-equal? (caddr tr) "Header"))

(test-case "a boolean external instance field gets a FieldSig with ELEMENT_TYPE_BOOLEAN"
  (define cp
    (module-with
     '((ldstr "a")
       (ldnull)
       (newobj (mscorlib System.Runtime.Remoting.Messaging.Header) (string object))
       (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) MustUnderstand boolean)
       (pop))))
  (check-equal? (caddr (car (memberref-named cp "MustUnderstand"))) (bytes #x06 #x02)))

(test-case "an object external instance field gets a FieldSig with ELEMENT_TYPE_OBJECT"
  (define cp
    (module-with
     '((ldstr "a")
       (ldnull)
       (newobj (mscorlib System.Runtime.Remoting.Messaging.Header) (string object))
       (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) Value object)
       (pop))))
  (check-equal? (caddr (car (memberref-named cp "Value"))) (bytes #x06 #x1c)))

(test-case "an external instance field read with no receiver on the stack underflows"
  (check-exn #rx"stack underflow"
             (λ () (module-with
                    '((ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
                      (pop))))))
