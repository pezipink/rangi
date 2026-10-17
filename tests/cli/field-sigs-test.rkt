#lang racket/base
; FieldSig blobs (ECMA-335 II.23.2.4) and their decoder. Expected bytes are derived by hand
; from the spec, not copied from the encoder's output.
(require rackunit
         "../../src/cli/sigs.rkt")

; ---------------------------------------------------------------------------
; encoding

(test-case "FieldSig of primitives: FIELD 0x06 then the type"
  (check-equal? (encode-field-sig 'int32) (bytes #x06 #x08))
  (check-equal? (encode-field-sig 'boolean) (bytes #x06 #x02))
  (check-equal? (encode-field-sig 'object) (bytes #x06 #x1C))
  (check-equal? (encode-field-sig 'string) (bytes #x06 #x0E)))

(test-case "a void field is rejected"
  (check-exn exn:fail? (λ () (encode-field-sig 'void))))

(test-case "CLASS typedef 1 uses TypeDefOrRefOrSpecEncoded (II.23.2.8): (1 << 2) | 0 = 4"
  (check-equal? (encode-field-sig '(class (typedef . 1))) (bytes #x06 #x12 #x04)))

(test-case "VALUETYPE typeref 3: (3 << 2) | 1 = 0x0D"
  (check-equal? (encode-field-sig '(valuetype (typeref . 3))) (bytes #x06 #x11 #x0D)))

(test-case "SZARRAY of CLASS typeref 2: (2 << 2) | 1 = 9"
  (check-equal? (encode-field-sig '(szarray (class (typeref . 2)))) (bytes #x06 #x1D #x12 #x09)))

(test-case "TypeDefOrRef boundary: typedef 32 is 0x80 (two-byte compressed form)"
  ; (32 << 2) | 0 = 128 = 0x80, encoded as 0x80 0x80
  (check-equal? (encode-field-sig '(class (typedef . 32))) (bytes #x06 #x12 #x80 #x80)))

(test-case "TypeDefOrRef boundary: typedef 4096 is 0x4000 (four-byte compressed form)"
  ; (4096 << 2) = 0x4000, encoded as C0 00 40 00
  (check-equal? (encode-field-sig '(class (typedef . 4096)))
                (bytes #x06 #x12 #xC0 #x00 #x40 #x00)))

(test-case "a GENERICINST field type reuses the type encoder"
  ; GENERICINST, CLASS, typedef 1, GenArgCount 1, I4
  (check-equal? (encode-field-sig '(genericinst (class (typedef . 1)) (int32)))
                (bytes #x06 #x15 #x12 #x04 #x01 #x08)))

(test-case "a BYREF field type encodes its element type"
  (check-equal? (encode-field-sig '(byref int32)) (bytes #x06 #x10 #x08)))

(test-case "a void SZARRAY element is rejected in a field type"
  (check-exn exn:fail? (λ () (encode-field-sig '(szarray void)))))

(test-case "custom modifiers keep their order: modreq typeref 1, then modopt typedef 1"
  ; FIELD, CMOD_REQD, typeref 1 (5), CMOD_OPT, typedef 1 (4), I4
  (check-equal? (encode-field-sig 'int32 #:custom-mods '((modreq (typeref . 1)) (modopt (typedef . 1))))
                (bytes #x06 #x1F #x05 #x20 #x04 #x08)))

(test-case "a bad custom modifier is rejected"
  (check-exn exn:fail? (λ () (encode-field-sig 'int32 #:custom-mods '((modfoo (typeref . 1)))))))

; ---------------------------------------------------------------------------
; decoding and round-trips

(test-case "decode-field-sig returns the type and an empty custom-mod list"
  (check-equal? (decode-field-sig (bytes #x06 #x08)) (field-signature '() 'int32))
  (check-equal? (decode-field-sig (bytes #x06 #x12 #x04)) (field-signature '() '(class (typedef . 1)))))

(test-case "decode-field-sig reads custom modifiers in blob order"
  (check-equal? (decode-field-sig (bytes #x06 #x1F #x05 #x20 #x04 #x08))
                (field-signature '((modreq (typeref . 1)) (modopt (typedef . 1))) 'int32)))

(test-case "decode-field-sig round-trips the encoder's output"
  (define types
    (list 'int32 'string 'object 'typedref
          '(class (typedef . 1))
          '(valuetype (typeref . 3))
          '(class (typespec . 1))
          '(szarray (class (typeref . 2)))
          '(szarray (szarray int32))
          '(byref (szarray int32))
          '(ptr object)
          '(mvar 0)
          '(var 2)
          '(genericinst (class (typedef . 1)) (int32 (var 0)))
          '(class (typedef . 4096))))
  (for ([t (in-list types)])
    (check-equal? (field-signature-type (decode-field-sig (encode-field-sig t))) t)))

(test-case "decode-field-sig round-trips custom modifiers"
  (define mods '((modreq (typeref . 1)) (modopt (typedef . 1))))
  (check-equal? (decode-field-sig (encode-field-sig 'int32 #:custom-mods mods))
                (field-signature mods 'int32)))

(test-case "decode-typespec agrees with the encoder for an SZARRAY of a class"
  (check-equal? (decode-typespec (bytes #x1D #x12 #x09)) '(szarray (class (typeref . 2)))))

(test-case "decode-field-sig rejects a blob that is not FIELD"
  ; LOCAL_SIG (0x07) is not a FieldSig
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x07 #x01 #x08)))))

(test-case "decode-field-sig rejects void"
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06 #x01)))))

(test-case "decode-field-sig rejects a pinned element as a field type"
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06 #x45 #x08)))))

(test-case "decode-field-sig rejects trailing bytes"
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06 #x08 #x00)))))

(test-case "decode-field-sig rejects a truncated blob"
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06))))
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06 #x12)))))

(test-case "decode-field-sig rejects a custom modifier with no token"
  (check-exn exn:fail? (λ () (decode-field-sig (bytes #x06 #x1F)))))
