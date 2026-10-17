#lang racket/base
; Signature blob encoders (ECMA-335 II.23.2). Expected bytes are derived by hand from the
; spec, not copied from the encoder's output.
(require rackunit
         "../../src/cli/sigs.rkt")

; ---------------------------------------------------------------------------
; compressed integers (II.23.2), reached through a VAR type (ELEMENT_TYPE_VAR, compressed index)

(define (var-bytes n) (encode-type (list 'var n)))

(test-case "compressed index: 1-byte form for 0 and 0x7F"
  (check-equal? (var-bytes 0) (bytes #x13 #x00))
  (check-equal? (var-bytes #x7F) (bytes #x13 #x7F)))

(test-case "compressed index: 2-byte form starts at 0x80 (10xxxxxx prefix)"
  ; 0x80 = 1000 0000 -> 0x80 | 0x00, then 0x80
  (check-equal? (var-bytes #x80) (bytes #x13 #x80 #x80))
  ; 0x3FFF = 0011 1111 1111 1111 -> 0x80 | 0x3F = 0xBF, then 0xFF
  (check-equal? (var-bytes #x3FFF) (bytes #x13 #xBF #xFF)))

(test-case "compressed index: 4-byte form starts at 0x4000 (110xxxxx prefix)"
  ; 0x4000 -> 0xC0 | 0x00, then 0x00 0x40 0x00
  (check-equal? (var-bytes #x4000) (bytes #x13 #xC0 #x00 #x40 #x00))
  ; 0x1FFFFFFF -> 0xC0 | 0x1F = 0xDF, then 0xFF 0xFF 0xFF
  (check-equal? (var-bytes #x1FFFFFFF) (bytes #x13 #xDF #xFF #xFF #xFF)))

(test-case "compressed integers above 0x1FFFFFFF are rejected"
  (check-exn exn:fail? (λ () (var-bytes #x20000000))))

; ---------------------------------------------------------------------------
; types

(test-case "primitive element types"
  (check-equal? (encode-type 'void) (bytes #x01))
  (check-equal? (encode-type 'int32) (bytes #x08))
  (check-equal? (encode-type 'object) (bytes #x1C))
  (check-equal? (encode-type 'string) (bytes #x0E))
  (check-equal? (encode-type 'float64) (bytes #x0D))
  (check-equal? (encode-type 'typedref) (bytes #x16)))

(test-case "CLASS and VALUETYPE use TypeDefOrRefOrSpecEncoded (II.23.2.8)"
  ; typedef rid 1: (1 << 2) | 0 = 4
  (check-equal? (encode-type '(class (typedef . 1))) (bytes #x12 #x04))
  ; typeref rid 3: (3 << 2) | 1 = 13 = 0x0D
  (check-equal? (encode-type '(valuetype (typeref . 3))) (bytes #x11 #x0D))
  ; typespec rid 1: (1 << 2) | 2 = 6
  (check-equal? (encode-type '(class (typespec . 1))) (bytes #x12 #x06)))

(test-case "SZARRAY, BYREF and PTR wrap their element type"
  (check-equal? (encode-type '(szarray int32)) (bytes #x1D #x08))
  (check-equal? (encode-type '(byref (szarray int32))) (bytes #x10 #x1D #x08))
  (check-equal? (encode-type '(ptr object)) (bytes #x0F #x1C)))

(test-case "MVAR takes a compressed index"
  (check-equal? (encode-type '(mvar 0)) (bytes #x1E #x00)))

(test-case "GENERICINST class typedef 1 with <int32, !0>"
  ; GENERICINST, CLASS, typedef 1 (0x04), GenArgCount 2, I4, VAR 0
  (check-equal? (encode-type '(genericinst (class (typedef . 1)) (int32 (var 0))))
                (bytes #x15 #x12 #x04 #x02 #x08 #x13 #x00)))

(test-case "GENERICINST valuetype typeref 3 with !!0"
  ; GENERICINST, VALUETYPE, typeref 3 (0x0D), GenArgCount 1, MVAR 0
  (check-equal? (encode-type '(genericinst (valuetype (typeref . 3)) ((mvar 0))))
                (bytes #x15 #x11 #x0D #x01 #x1E #x00)))

(test-case "TypeSpec blob: szarray of class typeref 2"
  ; SZARRAY, CLASS, typeref 2: (2 << 2) | 1 = 9
  (check-equal? (encode-typespec '(szarray (class (typeref . 2)))) (bytes #x1D #x12 #x09)))

(test-case "a void type argument is rejected in GENERICINST"
  (check-exn exn:fail? (λ () (encode-type '(genericinst (class (typedef . 1)) (void))))))

; ---------------------------------------------------------------------------
; method signatures (II.23.2.1)

(test-case "generic MethodDefSig with arity 1, returning and taking !!0"
  ; GENERIC 0x10, GenParamCount 1, ParamCount 1, RetType !!0, Param !!0
  (check-equal? (encode-method-sig '(mvar 0) '((mvar 0)) #:generic-arity 1)
                (bytes #x10 #x01 #x01 #x1E #x00 #x1E #x00)))

(test-case "instance method void(int32)"
  ; HASTHIS 0x20, ParamCount 1, RetType VOID, Param I4
  (check-equal? (encode-method-sig 'void '(int32) #:hasthis? #t)
                (bytes #x20 #x01 #x01 #x08)))

(test-case "static method with no parameters returning object"
  (check-equal? (encode-method-sig 'object '()) (bytes #x00 #x00 #x1C)))

(test-case "static method taking and returning int32[]"
  ; DEFAULT 0x00, ParamCount 1, RetType SZARRAY I4, Param SZARRAY I4
  (check-equal? (encode-method-sig '(szarray int32) '((szarray int32)))
                (bytes #x00 #x01 #x1D #x08 #x1D #x08)))

(test-case "VARARG: fixed params, then the sentinel, then the extra args (II.23.2.2)"
  ; VARARG 0x05, ParamCount 2 (fixed + extra), RetType I4, Param I4, SENTINEL 0x41, Param I4
  (check-equal? (encode-method-sig 'int32 '(int32 ... int32))
                (bytes #x05 #x02 #x08 #x08 #x41 #x08))
  (check-equal? (decode-method-sig (encode-method-sig 'int32 '(int32 ... int32)))
                (method-signature #f #f 0 'int32 '(int32 ... int32))))

(test-case "VARARG with no extras omits the sentinel and keeps the marker"
  (check-equal? (encode-method-sig 'void '(int32 ...)) (bytes #x05 #x01 #x01 #x08)))

(test-case "modreq and modopt wrap the parameter they modify (II.23.2.7)"
  ; DEFAULT, ParamCount 1, RetType modopt(void) -> CMOD_OPT 0x20, TypeRef 1 -> 0x05, VOID
  ; Param CMOD_REQD 0x1F, 0x05, I4
  (check-equal? (encode-method-sig '(modopt (typeref . 1) void) '((modreq (typeref . 1) int32)))
                (bytes #x00 #x01 #x20 #x05 #x01 #x1F #x05 #x08))
  (check-equal? (decode-method-sig (encode-method-sig '(modopt (typeref . 1) void)
                                                      '((modreq (typeref . 1) int32))))
                (method-signature #f #f 0 '(modopt (typeref . 1) void) '((modreq (typeref . 1) int32)))))

(test-case "FNPTR wraps a method signature (II.23.2.12)"
  ; FNPTR 0x1B, then DEFAULT sig: ParamCount 1, RetType VOID, Param I4
  (check-equal? (encode-type '(fnptr void (int32))) (bytes #x1B #x00 #x01 #x01 #x08)))

(test-case "a jagged array element nests SZARRAY: int32[][] is 1D 1D 08"
  (check-equal? (encode-type '(szarray (szarray int32))) (bytes #x1D #x1D #x08)))

(test-case "a szarray of void or typedref is rejected"
  (check-exn exn:fail? (λ () (encode-type '(szarray void))))
  (check-exn exn:fail? (λ () (encode-type '(szarray typedref)))))

; ---------------------------------------------------------------------------
; LocalVarSig (II.23.2.6)

(test-case "LocalVarSig with int32[] and int64[] locals"
  ; LOCAL_SIG 0x07, count 2, SZARRAY I4, SZARRAY I8
  (check-equal? (encode-localvar-sig '((szarray int32) (szarray int64)))
                (bytes #x07 #x02 #x1D #x08 #x1D #x0A)))

(test-case "LocalVarSig for (int32 object)"
  ; LOCAL_SIG 0x07, count 2, I4, OBJECT
  (check-equal? (encode-localvar-sig '(int32 object)) (bytes #x07 #x02 #x08 #x1C)))

(test-case "empty LocalVarSig"
  (check-equal? (encode-localvar-sig '()) (bytes #x07 #x00)))

(test-case "pinned byref szarray local: PINNED before BYREF"
  ; LOCAL_SIG, count 1, PINNED 0x45, BYREF 0x10, SZARRAY 0x1D, I4 0x08
  (check-equal? (encode-localvar-sig '((pinned (byref (szarray int32)))))
                (bytes #x07 #x01 #x45 #x10 #x1D #x08)))

(test-case "a void local is rejected"
  (check-exn exn:fail? (λ () (encode-localvar-sig '(void)))))

; ---------------------------------------------------------------------------
; MethodSpec instantiation (II.23.2.15)

(test-case "MethodSpec instantiation <int32, string>"
  ; GENERICINST 0x0A, GenArgCount 2, I4, STRING
  (check-equal? (encode-method-instantiation '(int32 string))
                (bytes #x0A #x02 #x08 #x0E)))

(test-case "MethodSpec instantiation <!!0>"
  (check-equal? (encode-method-instantiation '((mvar 0))) (bytes #x0A #x01 #x1E #x00)))

(test-case "an empty MethodSpec instantiation is rejected"
  (check-exn exn:fail? (λ () (encode-method-instantiation '()))))
