#lang racket/base
;; CIL instruction operand encoders. Opcode bytes and operand kinds come from
;; the table in opcodes.rkt; nothing here repeats opcode bytes.
;; Integers are little-endian (ECMA-335 II.22 and Partition III), and tokens
;; carry their table id in the high byte (II.3.2 "metadata tokens").

(require "opcodes.rkt")

(provide find-opcode
         opcode-named
         opcode-bytes
         operand-width
         instruction-length
         switch-instruction-length
         encode-instruction
         encode-int8
         encode-uint8
         encode-int16
         encode-uint16
         encode-int32
         encode-uint32
         encode-int64
         encode-float32
         encode-float64
         encode-token
         encode-switch-table
         encode-ldc-i4
         encode-var-access
         token-tags-method
         token-tags-field
         token-tags-type
         token-tags-tok
         token-tags-string
         token-tags-sig)

;; Metadata table ids (II.22) accepted by each token-carrying operand kind.
(define token-tags-method '(#x06 #x0A #x2B))            ; MethodDef, MemberRef, MethodSpec
(define token-tags-field '(#x04 #x0A))                  ; Field, MemberRef
(define token-tags-type '(#x01 #x02 #x1B))              ; TypeRef, TypeDef, TypeSpec
(define token-tags-tok '(#x01 #x02 #x04 #x06 #x0A #x1B #x2B))
(define token-tags-string '(#x70))                      ; #US heap, II.24.2.4
(define token-tags-sig '(#x11))                         ; StandAloneSig

(define opcodes-by-name
  (for/hasheq ([op (in-list opcode-table)])
    (values (opcode-name op) op)))

(define (find-opcode name)
  (hash-ref opcodes-by-name name #f))

(define (opcode-named name)
  (or (find-opcode name)
      (error 'opcode-named "unknown opcode: ~a" name)))

(define (opcode-bytes op)
  (define v (opcode-value op))
  (if (< v #x100)
      (bytes v)
      (bytes (quotient v 256) (remainder v 256))))

;; Width in bytes of a fixed-size operand, or #f when the operand is variable.
(define (operand-width op)
  (case (opcode-operand op)
    [(InlineNone) 0]
    [(ShortInlineI ShortInlineVar ShortInlineBrTarget) 1]
    [(InlineVar) 2]
    [(InlineI InlineBrTarget InlineMethod InlineField InlineType
      InlineTok InlineString InlineSig ShortInlineR) 4]
    [(InlineI8 InlineR) 8]
    [(InlineSwitch) #f]
    [else (error 'operand-width "unknown operand kind: ~a" (opcode-operand op))]))

(define (switch-instruction-length n)
  (+ (opcode-size (opcode-named 'switch)) 4 (* 4 n)))

;; Total encoded length for a given operand. For switch, the operand is the
;; list of offsets.
(define (instruction-length name [operand #f])
  (define op (opcode-named name))
  (cond
    [(eq? (opcode-operand op) 'InlineSwitch)
     (switch-instruction-length (length (or operand '())))]
    [else (+ (opcode-size op) (operand-width op))]))

;; Integer encoders. Each checks its range and emits little-endian bytes.
(define (int-bytes who v n signed?)
  (unless (exact-integer? v)
    (error who "expected an exact integer, got ~e" v))
  (define bits (* 8 n))
  (define-values (lo hi)
    (if signed?
        (values (- (expt 2 (sub1 bits))) (expt 2 (sub1 bits)))
        (values 0 (expt 2 bits))))
  (unless (and (<= lo v) (< v hi))
    (error who "~e does not fit in ~a ~a byte(s)" v (if signed? "signed" "unsigned") n))
  (define u (bitwise-and v (sub1 (expt 2 bits))))
  (apply bytes (for/list ([i (in-range n)])
                 (bitwise-and (arithmetic-shift u (* -8 i)) #xFF))))

(define (encode-int8 v) (int-bytes 'encode-int8 v 1 #t))
(define (encode-uint8 v) (int-bytes 'encode-uint8 v 1 #f))
(define (encode-int16 v) (int-bytes 'encode-int16 v 2 #t))
(define (encode-uint16 v) (int-bytes 'encode-uint16 v 2 #f))
(define (encode-int32 v) (int-bytes 'encode-int32 v 4 #t))
(define (encode-uint32 v) (int-bytes 'encode-uint32 v 4 #f))
(define (encode-int64 v) (int-bytes 'encode-int64 v 8 #t))

(define (encode-float32 v)
  (unless (real? v) (error 'encode-float32 "expected a real, got ~e" v))
  (real->floating-point-bytes v 4 #f))

(define (encode-float64 v)
  (unless (real? v) (error 'encode-float64 "expected a real, got ~e" v))
  (real->floating-point-bytes v 8 #f))

;; A metadata token is a table id in the high byte and a 1-based row index in
;; the low three bytes (II.3.2). Row 0 is the null token and is rejected.
(define (encode-token v allowed-tags)
  (unless (exact-integer? v)
    (error 'encode-token "expected a token integer, got ~e" v))
  (define tag (arithmetic-shift v -24))
  (unless (memv tag allowed-tags)
    (error 'encode-token "token ~x has table id ~x; expected one of ~a"
           v tag (map (lambda (t) (number->string t 16)) allowed-tags)))
  (when (zero? (bitwise-and v #xFFFFFF))
    (error 'encode-token "null token (row 0) is not allowed: ~x" v))
  (encode-uint32 v))

;; switch: uint32 count, then count int32 offsets (III.3.66).
(define (encode-switch-table offsets)
  (bytes-append (encode-uint32 (length offsets))
                (apply bytes-append (map encode-int32 offsets))))

;; Shortest form of ldc.i4 for an int32 value.
(define (encode-ldc-i4 v)
  (cond
    [(eqv? v -1) (encode-instruction 'ldc.i4.m1)]
    [(and (exact-integer? v) (<= 0 v 8))
     (encode-instruction (string->symbol (format "ldc.i4.~a" v)))]
    [(and (exact-integer? v) (<= -128 v 127))
     (encode-instruction 'ldc.i4.s v)]
    [else (encode-instruction 'ldc.i4 v)]))

;; Shortest form of an argument or local access. base is one of
;; ldarg, ldarga, starg, ldloc, ldloca, stloc.
(define (encode-var-access base index)
  (define base-name (symbol->string base))
  (define has-0-3? (member base-name '("ldarg" "ldloc" "stloc")))
  (define short-name (string->symbol (string-append base-name ".s")))
  (cond
    [(and has-0-3? (exact-integer? index) (<= 0 index 3))
     (encode-instruction (string->symbol (format "~a.~a" base-name index)))]
    [(and (exact-integer? index) (<= 0 index 255))
     (encode-instruction short-name index)]
    [else (encode-instruction base index)]))

(define (encode-operand op v)
  (define name (opcode-name op))
  (define (need)
    (unless v (error 'encode-instruction "~a requires an operand" name))
    v)
  (define (no-operand)
    (when v (error 'encode-instruction "~a takes no operand, got ~e" name v))
    #"")
  (case (opcode-operand op)
    [(InlineNone) (no-operand)]
    [(ShortInlineI)
     ;; unaligned. and no. take an unsigned byte; ldc.i4.s takes a signed one.
     (if (member (symbol->string name) '("unaligned." "no."))
         (encode-uint8 (need))
         (encode-int8 (need)))]
    [(InlineI) (encode-int32 (need))]
    [(InlineI8) (encode-int64 (need))]
    [(ShortInlineR) (encode-float32 (need))]
    [(InlineR) (encode-float64 (need))]
    [(ShortInlineVar) (encode-uint8 (need))]
    [(InlineVar) (encode-uint16 (need))]
    [(ShortInlineBrTarget) (encode-int8 (need))]
    [(InlineBrTarget) (encode-int32 (need))]
    [(InlineSwitch) (encode-switch-table (need))]
    [(InlineMethod) (encode-token (need) token-tags-method)]
    [(InlineField) (encode-token (need) token-tags-field)]
    [(InlineType) (encode-token (need) token-tags-type)]
    [(InlineTok) (encode-token (need) token-tags-tok)]
    [(InlineString) (encode-token (need) token-tags-string)]
    [(InlineSig) (encode-token (need) token-tags-sig)]
    [else (error 'encode-instruction "unknown operand kind: ~a" (opcode-operand op))]))

;; Encodes one instruction. For branch kinds the operand is the raw
;; displacement; label resolution lives in labels.rkt.
(define (encode-instruction name [operand #f])
  (define op (opcode-named name))
  (bytes-append (opcode-bytes op) (encode-operand op operand)))
