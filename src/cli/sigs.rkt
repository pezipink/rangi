#lang racket/base
; Signature blob encoders (ECMA-335 II.23.2). Pure functions from type descriptors to bytes.
;
; Type descriptors (shared with the reader, which decodes into the same shapes):
;   'void 'boolean 'char 'int8 'uint8 'int16 'uint16 'int32 'uint32 'int64 'uint64
;   'float32 'float64 'string 'object 'intptr 'uintptr 'typedref  primitives
;   (class tok) (valuetype tok)       tok is (cons table rid), table is typedef, typeref or typespec
;   (genericinst base (arg ...))      base is a class or valuetype descriptor
;   (var n) (mvar n)                  generic parameter by number (!n and !!n)
;   (szarray t) (byref t) (ptr t)
;   (pinned t)                        only as a top-level local in a LocalVarSig
(require "schema.rkt"
         "../private/binary.rkt")
(provide element-codes
         callconv-codes
         primitive-names
         encode-type
         encode-typespec
         encode-method-sig
         encode-localvar-sig
         encode-method-instantiation)

; II.23.1.16 element types, and the composite element types from II.23.2
(define element-codes
  '((void . #x01) (boolean . #x02) (char . #x03) (int8 . #x04) (uint8 . #x05)
    (int16 . #x06) (uint16 . #x07) (int32 . #x08) (uint32 . #x09) (int64 . #x0A)
    (uint64 . #x0B) (float32 . #x0C) (float64 . #x0D) (string . #x0E)
    (ptr . #x0F) (byref . #x10) (valuetype . #x11) (class . #x12) (var . #x13)
    (genericinst . #x15) (typedref . #x16) (intptr . #x18) (uintptr . #x19)
    (object . #x1C) (szarray . #x1D) (mvar . #x1E) (pinned . #x45)))

; II.23.2.1 and II.23.2.6 calling convention bits and signature kinds
(define callconv-codes
  '((default . #x00) (vararg . #x05) (generic . #x10) (localsig . #x07)
    (hasthis . #x20) (explicitthis . #x40) (genericinst . #x0A)))

(define primitive-names
  '(void boolean char int8 uint8 int16 uint16 int32 uint32 int64 uint64
    float32 float64 string object intptr uintptr typedref))

(define (element-code name)
  (cond
    [(assq name element-codes) => cdr]
    [else (error 'sigs "no element type code for ~a" name)]))

(define (callconv-code name) (cdr (assq name callconv-codes)))

; A class or valuetype token is TypeDefOrRefOrSpecEncoded, a compressed integer (II.23.2.8)
(define (typedeforref-bytes tok)
  (unless (and (pair? tok) (exact-nonnegative-integer? (cdr tok)))
    (error 'sigs "bad type token ~s" tok))
  (compress-unsigned (coded-encode 'typedeforref (car tok) (cdr tok))))

; Encodes one Type (II.23.2.12). Custom modifiers and ARRAY are not supported yet.
(define (encode-type t)
  (cond
    [(memq t primitive-names) (bytes (element-code t))]
    [(symbol? t) (error 'sigs "not a primitive type: ~a" t)]
    [(not (pair? t)) (error 'sigs "bad type descriptor ~s" t)]
    [else
     (case (car t)
       [(class valuetype)
        (bytes-append (bytes (element-code (car t))) (typedeforref-bytes (cadr t)))]
       [(genericinst)
        (define base (cadr t))
        (unless (and (pair? base) (memq (car base) '(class valuetype)))
          (error 'sigs "GENERICINST base must be a class or valuetype: ~s" base))
        (define args (caddr t))
        (unless (and (pair? args) (not (memq 'void args)))
          (error 'sigs "GENERICINST needs at least one non-void argument: ~s" args))
        (apply bytes-append (bytes (element-code 'genericinst)) (encode-type base)
               (compress-unsigned (length args))
               (map encode-type args))]
       [(var mvar)
        (bytes-append (bytes (element-code (car t))) (compress-unsigned (cadr t)))]
       [(szarray byref ptr)
        (bytes-append (bytes (element-code (car t))) (encode-type (cadr t)))]
       [else (error 'sigs "bad type descriptor ~s" t)])]))

; II.23.2.14: a TypeSpec blob is one Type
(define (encode-typespec t) (encode-type t))

; II.23.2.1 MethodDefSig and MethodRefSig. The GENERIC flag and GenParamCount appear
; only when arity is above zero. VARARG and the sentinel are not supported yet.
(define (encode-method-sig ret params
                           #:hasthis? [hasthis? #f]
                           #:explicitthis? [explicitthis? #f]
                           #:generic-arity [arity 0])
  (for ([p (in-list params)])
    (when (eq? p 'void) (error 'sigs "void is not a parameter type")))
  (define cc
    (bitwise-ior (if hasthis? (callconv-code 'hasthis) 0)
                 (if explicitthis? (callconv-code 'explicitthis) 0)
                 (if (> arity 0) (callconv-code 'generic) 0)))
  (apply bytes-append
         (bytes cc)
         (if (> arity 0) (compress-unsigned arity) #"")
         (compress-unsigned (length params))
         (encode-type ret)
         (map encode-type params)))

; II.23.2.6 LocalVarSig: LOCAL_SIG, the count, then one LOCAL_VAR per local. A local is
; [PINNED] [BYREF] Type, or TYPEDBYREF.
(define (encode-localvar-sig locals)
  (apply bytes-append
         (bytes (callconv-code 'localsig))
         (compress-unsigned (length locals))
         (map encode-local locals)))

(define (encode-local t)
  (cond
    [(and (pair? t) (eq? (car t) 'pinned))
     (bytes-append (bytes (element-code 'pinned)) (encode-local (cadr t)))]
    [(eq? t 'void) (error 'sigs "void is not a local type")]
    [else (encode-type t)]))

; II.23.2.15 MethodSpec instantiation: GENERICINST, GenArgCount, Type+
(define (encode-method-instantiation args)
  (unless (pair? args) (error 'sigs "a MethodSpec needs at least one type argument"))
  (apply bytes-append
         (bytes (callconv-code 'genericinst))
         (compress-unsigned (length args))
         (map encode-type args)))
