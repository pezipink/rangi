#lang racket/base
; Multi-dimensional arrays (II.14.2, II.23.2.13). Expected bytes are derived by hand from the
; spec: ARRAY is ELEMENT_TYPE_ARRAY (0x14), elem type, ArrayShape = Rank, NumSizes, sizes,
; NumLoBounds, lobounds. The zero-size, zero-bound form is 14 ELEM R 00 00.
(require rackunit
         racket/list
         "../../src/cli/sigs.rkt"
         "../../src/cli/lower.rkt"
         "../../src/ilasm/syntax.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program-with . body-forms)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) ,@body-forms (ret) })]))))

(define (lower-error-msg . body-forms)
  (with-handlers ([exn:fail? exn-message])
    (lower-module (apply program-with body-forms))
    #f))

; ---------------------------------------------------------------------------
; signature encoding

(test-case "ARRAY of int32 with rank 2 and no sizes or bounds"
  (check-equal? (encode-type '(array int32 2)) (bytes #x14 #x08 #x02 #x00 #x00)))

(test-case "ARRAY rank is a compressed integer, so rank 0x80 takes two bytes"
  (check-equal? (encode-type '(array int32 #x80)) (bytes #x14 #x08 #x80 #x80 #x00 #x00)))

(test-case "ARRAY of a class element encodes the element type first"
  (check-equal? (encode-type '(array (class (typeref . 3)) 3))
                (bytes #x14 #x12 #x0D #x03 #x00 #x00)))

(test-case "ARRAY rank must be a positive integer"
  (check-exn exn:fail? (λ () (encode-type '(array int32 0))))
  (check-exn exn:fail? (λ () (encode-type '(array int32 -1)))))

(test-case "ARRAY of void or typedref is rejected"
  (check-exn exn:fail? (λ () (encode-type '(array void 2))))
  (check-exn exn:fail? (λ () (encode-type '(array typedref 2)))))

(test-case "decoding an ARRAY gives its element and rank"
  (check-equal? (decode-typespec (bytes #x14 #x08 #x02 #x00 #x00)) '(array int32 2)))

(test-case "decoding round-trips a rank-3 ARRAY"
  (check-equal? (decode-typespec (encode-typespec '(array int32 3))) '(array int32 3)))

; Signed compressed integers (II.23.2): 3 -> 06, -3 -> 7B, -64 -> 01, 64 -> 80 80, -8192 -> 80 01.
(test-case "signed compressed integers use 7, 14 or 29 bits with the sign in bit 0"
  (check-equal? (compress-signed 3) (bytes #x06))
  (check-equal? (compress-signed -3) (bytes #x7B))
  (check-equal? (compress-signed -64) (bytes #x01))
  (check-equal? (compress-signed 64) (bytes #x80 #x80))
  (check-equal? (compress-signed -8192) (bytes #x80 #x01))
  (check-exn exn:fail? (λ () (compress-signed 268435456)))
  (check-exn exn:fail? (λ () (compress-signed -268435457))))

; Bounded ARRAY (II.23.2.13): Rank 2, NumSizes 2 (10 20), NumLoBounds 2 (0 5)
(test-case "a bounded ARRAY encodes its sizes and signed lower bounds"
  (check-equal? (encode-type '(array int32 2 (10 20) (0 5)))
                (bytes #x14 #x08 #x02 #x02 #x0A #x14 #x02 #x00 #x0A)))

(test-case "a bounded ARRAY with negative lower bounds encodes them as signed integers"
  (check-equal? (encode-type '(array int32 1 (4) (-3)))
                (bytes #x14 #x08 #x01 #x01 #x04 #x01 #x7B)))

(test-case "a bounded ARRAY needs sizes and lower bounds each empty or one per dimension"
  (check-exn exn:fail? (λ () (encode-type '(array int32 2 (1) (0)))))
  (check-exn exn:fail? (λ () (encode-type '(array int32 2 (1 2) (0 0 0))))))

(test-case "a bounded ARRAY round-trips through decode"
  (for ([t (list '(array int32 2 (10 20) (0 5))
                 '(array int32 2 (3 4) ())
                 '(array int32 2 () (1 -1))
                 '(array (class (typeref . 3)) 3 (2 2 2) (-1 0 1)))])
    (check-equal? (decode-typespec (encode-typespec t)) t)))

(test-case "decoding rejects ARRAY sizes or lower bounds that do not match the rank"
  ; rank 2, NumSizes 1, size 4
  (check-exn #rx"empty or one per dimension"
             (λ () (decode-typespec (bytes #x14 #x08 #x02 #x01 #x04 #x00))))
  ; rank 2, NumLoBounds 1, lower bound 0
  (check-exn #rx"empty or one per dimension"
             (λ () (decode-typespec (bytes #x14 #x08 #x02 #x00 #x01 #x00))))
  ; rank 0 is not a valid ArrayShape
  (check-exn exn:fail? (λ () (decode-typespec (bytes #x14 #x08 #x00 #x00 #x00)))))

; ---------------------------------------------------------------------------
; lowering: TypeSpec parent and member signatures

(define (memberref-rows cp) (cli-program-memberrefs cp))
(define (typespec-blob cp rid) (list-ref (cli-program-typespecs cp) (sub1 rid)))

(define (method-named? row name) (equal? (cadr row) name))

; MemberRef names are stored as strings (II.22.25 Name is a #string index).
(define (memberref-named cp name)
  (findf (λ (r) (method-named? r name)) (memberref-rows cp)))

(test-case "a multi-dimensional array method is a MemberRef on a TypeSpec parent"
  (define cp (lower-module (program-with '(ldc.i4.2) '(ldc.i4.3)
                                         '(newobj (array int32 2) (int32 int32)) '(pop))))
  (define row (memberref-named cp ".ctor"))
  (check-true (pair? row))
  (define parent (car row))
  (check-equal? (car parent) 'typespec)
  (check-equal? (decode-typespec (typespec-blob cp (cdr parent))) '(array int32 2)))

(test-case "the constructor signature takes one int32 per dimension and returns void"
  (define cp (lower-module (program-with '(ldc.i4.2) '(ldc.i4.3)
                                         '(newobj (array int32 2) (int32 int32)) '(pop))))
  (check-equal? (caddr (memberref-named cp ".ctor")) (bytes #x20 #x02 #x01 #x08 #x08)))

(test-case "Get returns the element and takes the indices"
  (define cp (lower-module (program-with '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                         '(call instance int32 (array int32 2) Get (int32 int32))
                                         '(pop))))
  (check-equal? (caddr (memberref-named cp "Get")) (bytes #x20 #x02 #x08 #x08 #x08)))

(test-case "Set returns void and takes the indices then the element"
  (define cp (lower-module (program-with '(ldnull) '(ldc.i4.0) '(ldc.i4.0) '(ldc.i4.5)
                                         '(call instance void (array int32 2) Set (int32 int32 int32)))))
  (check-equal? (caddr (memberref-named cp "Set")) (bytes #x20 #x03 #x01 #x08 #x08 #x08)))

(test-case "Address returns a byref to the element and takes the indices"
  (define cp (lower-module (program-with '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                         '(call instance (byref int32) (array int32 2) Address (int32 int32))
                                         '(pop))))
  (check-equal? (caddr (memberref-named cp "Address")) (bytes #x20 #x02 #x10 #x08 #x08 #x08)))

(test-case "a rank-3 array's Get takes three indices"
  (define cp (lower-module (program-with '(ldnull) '(ldc.i4.0) '(ldc.i4.0) '(ldc.i4.0)
                                         '(call instance int32 (array int32 3) Get (int32 int32 int32))
                                         '(pop))))
  (check-equal? (caddr (memberref-named cp "Get")) (bytes #x20 #x03 #x08 #x08 #x08 #x08)))

(test-case "the array methods need the instance keyword"
  (check-regexp-match #rx"needs the instance keyword"
                      (or (lower-error-msg '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                           '(call int32 (array int32 2) Get (int32 int32)) '(pop))
                          "")))

(test-case "an array method with the wrong signature is rejected"
  (check-regexp-match #rx"must have return"
                      (or (lower-error-msg '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                           '(call instance int64 (array int32 2) Get (int32 int32)) '(pop))
                          "")))

(test-case "an unknown array method is rejected"
  (check-regexp-match #rx"has no method Foo"
                      (or (lower-error-msg '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                           '(call instance int32 (array int32 2) Foo (int32 int32)) '(pop))
                          "")))

(test-case "a newobj of a multi-dimensional array with the wrong constructor arguments is rejected"
  (check-regexp-match #rx"must have return"
                      (or (lower-error-msg '(ldc.i4.2) '(newobj (array int32 2) (int32))
                                           '(pop))
                          "")))

(test-case "ldvirtftn on an array method is rejected"
  (check-regexp-match #rx"not allowed on an array method"
                      (or (lower-error-msg '(ldnull) '(ldvirtftn int32 (array int32 2) Get (int32 int32)))
                          "")))

(test-case "a bounded array's pair constructor takes lower bound and size per dimension"
  (define cp (lower-module (program-with '(ldc.i4.5) '(ldc.i4.2) '(ldc.i4.3) '(ldc.i4.3)
                                         '(newobj (array int32 2 (2 3) (5 3)) (int32 int32 int32 int32))
                                         '(pop))))
  (check-equal? (caddr (memberref-named cp ".ctor")) (bytes #x20 #x04 #x01 #x08 #x08 #x08 #x08)))

(test-case "a bounded array's parent TypeSpec keeps its sizes and lower bounds"
  (define cp (lower-module (program-with '(ldnull) '(ldc.i4.0) '(ldc.i4.0)
                                         '(call instance int32 (array int32 2 (2 3) (5 3)) Get (int32 int32))
                                         '(pop))))
  (define parent (car (memberref-named cp "Get")))
  (check-equal? (car parent) 'typespec)
  (check-equal? (decode-typespec (typespec-blob cp (cdr parent)))
                '(array int32 2 (2 3) (5 3))))

(test-case "a bounded array's pair constructor with three int32s is rejected"
  (check-regexp-match #rx"must have return"
                      (or (lower-error-msg '(ldc.i4.5) '(ldc.i4.2) '(ldc.i4.3)
                                           '(newobj (array int32 2 (2 3) (5 3)) (int32 int32 int32))
                                           '(pop))
                          "")))
