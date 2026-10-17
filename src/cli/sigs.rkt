#lang racket/base
; Signature blob encoders and decoders (ECMA-335 II.23.2). The encoders are pure functions
; from type descriptors to bytes; the decoders invert them and share the same descriptors.
;
; Type descriptors (the decoders produce the same shapes):
;   'void 'boolean 'char 'int8 'uint8 'int16 'uint16 'int32 'uint32 'int64 'uint64
;   'float32 'float64 'string 'object 'intptr 'uintptr 'typedref  primitives
;   (class tok) (valuetype tok)       tok is (cons table rid), table is typedef, typeref or typespec
;   (genericinst base (arg ...))      base is a class or valuetype descriptor
;   (var n) (mvar n)                  generic parameter by number (!n and !!n)
;   (szarray t) (byref t) (ptr t)
;   (array t rank)                    multi-dimensional, zero lower bounds and no sizes (II.23.2.13)
;   (array t rank sizes lobounds)     bounded: sizes and lower bounds, each empty or one per dimension
;   (pinned t)                        only as a top-level local in a LocalVarSig
;
; Custom modifiers (II.23.2.7) are (modreq tok) or (modopt tok), with tok as above.
(require "schema.rkt"
         "../private/binary.rkt")
(provide element-codes
         callconv-codes
         primitive-names
         encode-type
         encode-typespec
         compress-signed
         encode-method-sig
         encode-property-sig
         encode-localvar-sig
         encode-method-instantiation
         encode-field-sig
         (struct-out field-signature)
         (struct-out method-signature)
         decode-typespec
         decode-method-sig
         decode-localvar-sig
         decode-method-instantiation
         decode-field-sig)

; II.23.1.16 element types, and the composite element types from II.23.2
(define element-codes
  '((void . #x01) (boolean . #x02) (char . #x03) (int8 . #x04) (uint8 . #x05)
    (int16 . #x06) (uint16 . #x07) (int32 . #x08) (uint32 . #x09) (int64 . #x0A)
    (uint64 . #x0B) (float32 . #x0C) (float64 . #x0D) (string . #x0E)
    (ptr . #x0F) (byref . #x10) (valuetype . #x11) (class . #x12) (var . #x13)
    (genericinst . #x15) (typedref . #x16) (intptr . #x18) (uintptr . #x19)
    (object . #x1C) (array . #x14) (szarray . #x1D) (mvar . #x1E) (pinned . #x45)
    ; II.23.1.16 custom modifier markers (II.23.2.7)
    (cmod-reqd . #x1F) (cmod-opt . #x20)))

; II.23.2.1, II.23.2.4, II.23.2.6 and II.23.2.15 calling convention bits and signature kinds
(define callconv-codes
  '((default . #x00) (vararg . #x05) (generic . #x10) (localsig . #x07) (field . #x06)
    (property . #x08) (hasthis . #x20) (explicitthis . #x40) (genericinst . #x0A)))

(define primitive-names
  '(void boolean char int8 uint8 int16 uint16 int32 uint32 int64 uint64
    float32 float64 string object intptr uintptr typedref))

(define (element-code name)
  (cond
    [(assq name element-codes) => cdr]
    [else (error 'sigs "no element type code for ~a" name)]))

(define (callconv-code name) (cdr (assq name callconv-codes)))

; II.23.2 signed compressed integer. The value is a two's complement number of 7, 14 or 29 bits,
; rotated one bit left so the sign bit lands in bit 0. Range is -2^28 to 2^28-1.
(define (compress-signed v)
  (define bits
    (cond
      [(<= -64 v 63) 7]
      [(<= -8192 v 8191) 14]
      [(<= -268435456 v 268435455) 29]
      [else (error 'sigs "signed ARRAY bound out of range: ~a" v)]))
  (define mask (sub1 (arithmetic-shift 1 bits)))
  (define u (bitwise-and v mask))
  (define r (bitwise-ior (bitwise-and (arithmetic-shift u 1) mask)
                         (arithmetic-shift u (- 1 bits))))
  (case bits
    [(7) (bytes r)]
    [(14) (bytes (bitwise-ior #x80 (arithmetic-shift r -8)) (bitwise-and r #xFF))]
    [else (bytes (bitwise-ior #xC0 (arithmetic-shift r -24))
                 (bitwise-and (arithmetic-shift r -16) #xFF)
                 (bitwise-and (arithmetic-shift r -8) #xFF)
                 (bitwise-and r #xFF))]))

; A class or valuetype token is TypeDefOrRefOrSpecEncoded, a compressed integer (II.23.2.8)
(define (typedeforref-bytes tok)
  (unless (and (pair? tok) (exact-nonnegative-integer? (cdr tok)))
    (error 'sigs "bad type token ~s" tok))
  (compress-unsigned (coded-encode 'typedeforref (car tok) (cdr tok))))

; Encodes one Type (II.23.2.12). Custom modifiers are not supported. SZARRAY and ARRAY, with or
; without sizes and lower bounds, are.
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
       [(szarray)
        (when (memq (cadr t) '(void typedref))
          (error 'sigs "SZARRAY element type cannot be ~a" (cadr t)))
        (bytes-append (bytes (element-code 'szarray)) (encode-type (cadr t)))]
       [(array)
        (unless (memv (length t) '(3 5))
          (error 'sigs "ARRAY must be (array ELEM RANK) or (array ELEM RANK SIZES LOBOUNDS): ~s" t))
        (define elem (cadr t))
        (define rank (caddr t))
        (define sizes (if (= (length t) 5) (list-ref t 3) '()))
        (define lobounds (if (= (length t) 5) (list-ref t 4) '()))
        (when (memq elem '(void typedref))
          (error 'sigs "ARRAY element type cannot be ~a" elem))
        (unless (and (exact-integer? rank) (>= rank 1))
          (error 'sigs "ARRAY rank must be a positive integer: ~s" rank))
        (for ([s (in-list sizes)])
          (unless (and (exact-nonnegative-integer? s) (<= s #x1FFFFFFF))
            (error 'sigs "ARRAY size must be a non-negative integer: ~s" s)))
        (for ([l (in-list lobounds)])
          (unless (exact-integer? l)
            (error 'sigs "ARRAY lower bound must be an integer: ~s" l)))
        (for ([l (in-list (list sizes lobounds))])
          (unless (memv (length l) (list 0 rank))
            (error 'sigs "ARRAY sizes and lower bounds must be empty or one per dimension: ~s" t)))
        ; II.23.2.13 ArrayShape: Rank, NumSizes, Sizes, NumLoBounds, LoBounds
        (bytes-append (bytes (element-code 'array)) (encode-type elem)
                      (compress-unsigned rank)
                      (compress-unsigned (length sizes))
                      (apply bytes-append (map compress-unsigned sizes))
                      (compress-unsigned (length lobounds))
                      (apply bytes-append (map compress-signed lobounds)))]
       [(byref ptr)
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

; II.23.2.5 PropertySig: PROPERTY (plus HASTHIS for an instance property), ParamCount, the
; property Type, then the index Types. Its layout matches MethodDefSig, so no GENERIC bit.
(define (encode-property-sig type params #:hasthis? [hasthis? #f])
  (unless (list? params) (error 'sigs "malformed property parameter list ~s" params))
  (apply bytes-append
         (bytes (bitwise-ior (callconv-code 'property) (if hasthis? (callconv-code 'hasthis) 0)))
         (compress-unsigned (length params))
         (encode-type type)
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

; II.23.2.4 FieldSig: FIELD, CustomMod*, Type. Void is not a field type.
(struct field-signature (custom-mods type) #:transparent)

(define (encode-field-sig t #:custom-mods [mods '()])
  (when (eq? t 'void) (error 'sigs "void is not a field type"))
  (apply bytes-append
         (bytes (callconv-code 'field))
         (append (map encode-custom-mod mods) (list (encode-type t)))))

; II.23.2.7 CustomMod: CMOD_REQD or CMOD_OPT, then a TypeDefOrRef token
(define (encode-custom-mod m)
  (unless (and (pair? m) (memq (car m) '(modreq modopt)))
    (error 'sigs "bad custom modifier ~s" m))
  (bytes-append (bytes (element-code (if (eq? (car m) 'modreq) 'cmod-reqd 'cmod-opt)))
                (typedeforref-bytes (cadr m))))

; Decoders (II.23.2). They mirror the encoders above and reject anything the encoders never
; produce. Each decoder consumes the whole blob, so trailing bytes are an error.
(struct method-signature (hasthis? explicitthis? generic-arity ret params) #:transparent)

(define (sig-byte who port)
  (define b (read-byte port))
  (when (eof-object? b) (error who "truncated signature"))
  b)

; II.23.2 compressed unsigned integer: one, two or four bytes
(define (sig-compressed who port)
  (define b0 (sig-byte who port))
  (cond
    [(zero? (bitwise-and b0 #x80)) b0]
    [(= (bitwise-and b0 #xC0) #x80)
     (+ (* (bitwise-and b0 #x3F) 256) (sig-byte who port))]
    [(= (bitwise-and b0 #xE0) #xC0)
     (let* ([b1 (sig-byte who port)]
            [b2 (sig-byte who port)]
            [b3 (sig-byte who port)])
       (+ (* (bitwise-and b0 #x1F) 16777216) (* b1 65536) (* b2 256) b3))]
    [else (error who "invalid compressed integer lead byte 0x~a" (number->string b0 16))]))

; II.23.2 signed compressed integer, the inverse of compress-signed
(define (sig-signed who port)
  (define b0 (sig-byte who port))
  (define-values (bits r)
    (cond
      [(zero? (bitwise-and b0 #x80)) (values 7 b0)]
      [(= (bitwise-and b0 #xC0) #x80)
       (values 14 (+ (* (bitwise-and b0 #x3F) 256) (sig-byte who port)))]
      [(= (bitwise-and b0 #xE0) #xC0)
       (let* ([b1 (sig-byte who port)]
              [b2 (sig-byte who port)]
              [b3 (sig-byte who port)])
         (values 29 (+ (* (bitwise-and b0 #x1F) 16777216) (* b1 65536) (* b2 256) b3)))]
      [else (error who "invalid signed integer lead byte 0x~a" (number->string b0 16))]))
  (define u (bitwise-ior (arithmetic-shift r -1) (arithmetic-shift (bitwise-and r 1) (sub1 bits))))
  (if (>= u (arithmetic-shift 1 (sub1 bits))) (- u (arithmetic-shift 1 bits)) u))

(define (sig-element-name who code)
  (or (for/first ([e (in-list element-codes)] #:when (= (cdr e) code)) (car e))
      (error who "unknown element type 0x~a" (number->string code 16))))

; II.23.2.8 TypeDefOrRefOrSpecEncoded
(define (sig-typedeforref who port)
  (define v (sig-compressed who port))
  (define-values (target rid) (coded-decode (coded-kind-by-name 'typedeforref) v))
  (unless target (error who "unused TypeDefOrRef tag for ~a" v))
  (cons target rid))

; II.23.2.12 Type
(define (sig-type who port)
  (define name (sig-element-name who (sig-byte who port)))
  (cond
    [(memq name primitive-names) name]
    [else
     (case name
       [(class valuetype) (list name (sig-typedeforref who port))]
       [(genericinst)
        (define base (sig-type who port))
        (unless (and (pair? base) (memq (car base) '(class valuetype)))
          (error who "GENERICINST base must be a class or valuetype"))
        (define n (sig-compressed who port))
        (when (zero? n) (error who "GENERICINST with no arguments"))
        (list 'genericinst base
              (for/list ([i (in-range n)])
                (define t (sig-type who port))
                (when (eq? t 'void) (error who "void GENERICINST argument"))
                t))]
       [(var mvar) (list name (sig-compressed who port))]
       [(szarray byref ptr) (list name (sig-type who port))]
       [(array)
        (define elem (sig-type who port))
        (when (memq elem '(void typedref)) (error who "ARRAY element type cannot be ~a" elem))
        (define rank (sig-compressed who port))
        (when (zero? rank) (error who "ARRAY rank must be positive"))
        ; II.23.2.13 ArrayShape. Sizes and lower bounds are each empty or one per dimension, as the
        ; encoder writes them.
        (define nsizes (sig-compressed who port))
        (define sizes (for/list ([i (in-range nsizes)]) (sig-compressed who port)))
        (define nlobounds (sig-compressed who port))
        (define lobounds (for/list ([i (in-range nlobounds)]) (sig-signed who port)))
        (for ([l (in-list (list sizes lobounds))])
          (unless (memv (length l) (list 0 rank))
            (error who "ARRAY sizes and lower bounds must be empty or one per dimension")))
        (if (and (null? sizes) (null? lobounds))
            (list 'array elem rank)
            (list 'array elem rank sizes lobounds))]
       [else (error who "unsupported element type ~a" name)])]))

; II.23.2.7 CustomMod*, as (modreq tok) and (modopt tok) pairs in blob order
(define (sig-custom-mods who port)
  (define reqd (cdr (assq 'cmod-reqd element-codes)))
  (define opt (cdr (assq 'cmod-opt element-codes)))
  (let loop ([acc '()])
    (define b (peek-byte port))
    (cond
      [(or (eqv? b reqd) (eqv? b opt))
       (read-byte port)
       (define tok (sig-typedeforref who port))
       (loop (cons (list (if (eqv? b reqd) 'modreq 'modopt) tok) acc))]
      [else (reverse acc)])))

(define (decode-whole who bs proc)
  (define port (open-input-bytes bs))
  (define v (proc port))
  (unless (eof-object? (peek-byte port)) (error who "trailing bytes after signature"))
  v)

; II.23.2.14 TypeSpec blob: one Type
(define (decode-typespec bs)
  (decode-whole 'decode-typespec bs (λ (port) (sig-type 'decode-typespec port))))

; II.23.2.4 FieldSig
(define (decode-field-sig bs)
  (define who 'decode-field-sig)
  (decode-whole
   who bs
   (λ (port)
     (define cc (sig-byte who port))
     (unless (= cc (cdr (assq 'field callconv-codes)))
       (error who "not a FieldSig: 0x~a" (number->string cc 16)))
     (define mods (sig-custom-mods who port))
     (define t (sig-type who port))
     (when (eq? t 'void) (error who "void is not a field type"))
     (field-signature mods t))))

; II.23.2.1 MethodDefSig / MethodRefSig
(define (decode-method-sig bs)
  (define who 'decode-method-sig)
  (decode-whole
   who bs
   (λ (port)
     (define cc (sig-byte who port))
     ; only HASTHIS (0x20), EXPLICITTHIS (0x40) and GENERIC (0x10) are supported; the kind is default
     (unless (zero? (bitwise-and cc #x8F))
       (error who "unsupported calling convention 0x~a" (number->string cc 16)))
     (define generic? (positive? (bitwise-and cc #x10)))
     (define arity
       (cond
         [generic?
          (let ([a (sig-compressed who port)])
            (when (zero? a) (error who "GENERIC signature with zero generic parameters"))
            a)]
         [else 0]))
     (define nparams (sig-compressed who port))
     (define ret (sig-type who port))
     (define params
       (for/list ([i (in-range nparams)])
         (define t (sig-type who port))
         (when (eq? t 'void) (error who "void is not a parameter type"))
         t))
     (method-signature (positive? (bitwise-and cc #x20))
                       (positive? (bitwise-and cc #x40))
                       arity ret params))))

; II.23.2.6 LocalVarSig
(define (decode-localvar-sig bs)
  (define who 'decode-localvar-sig)
  (decode-whole
   who bs
   (λ (port)
     (define cc (sig-byte who port))
     (unless (= cc (cdr (assq 'localsig callconv-codes)))
       (error who "not a LocalVarSig: 0x~a" (number->string cc 16)))
     (define n (sig-compressed who port))
     (for/list ([i (in-range n)]) (sig-local who port)))))

(define (sig-local who port)
  (cond
    [(eqv? (peek-byte port) (cdr (assq 'pinned element-codes)))
     (read-byte port)
     (list 'pinned (sig-local who port))]
    [else
     (define t (sig-type who port))
     (when (eq? t 'void) (error who "void is not a local type"))
     t]))

; II.23.2.15 MethodSpec instantiation
(define (decode-method-instantiation bs)
  (define who 'decode-method-instantiation)
  (decode-whole
   who bs
   (λ (port)
     (define cc (sig-byte who port))
     (unless (= cc (cdr (assq 'genericinst callconv-codes)))
       (error who "not a MethodSpec instantiation: 0x~a" (number->string cc 16)))
     (define n (sig-compressed who port))
     (when (zero? n) (error who "MethodSpec needs at least one type argument"))
     (for/list ([i (in-range n)]) (sig-type who port)))))

