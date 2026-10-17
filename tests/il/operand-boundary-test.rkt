#lang racket/base
;; Boundary tests for the operand encoders and the ldc.i4 / variable-access
;; macro selectors. Expected bytes are written out by hand from the operand
;; widths and signedness in ECMA-335 Partition III and the opcode bytes in
;; src/il/opcodes.rkt; they are not copied from the encoder's output.
;; Integers are little-endian.
(require rackunit
         "../../src/il/encode.rkt")

(define (fail-encoding name operand)
  (check-exn exn:fail? (lambda () (encode-instruction name operand))))

;; ---------------------------------------------------------------------------
;; Integer operand encoders: exact range limits
(check-equal? (encode-int8 -128) (bytes #x80))
(check-equal? (encode-int8 127) (bytes #x7F))
(check-exn exn:fail? (lambda () (encode-int8 -129)))
(check-exn exn:fail? (lambda () (encode-int8 128)))
(check-exn exn:fail? (lambda () (encode-int8 1.0)))

(check-equal? (encode-uint8 0) (bytes #x00))
(check-equal? (encode-uint8 255) (bytes #xFF))
(check-exn exn:fail? (lambda () (encode-uint8 -1)))
(check-exn exn:fail? (lambda () (encode-uint8 256)))

(check-equal? (encode-int16 -32768) (bytes #x00 #x80))
(check-equal? (encode-int16 32767) (bytes #xFF #x7F))
(check-exn exn:fail? (lambda () (encode-int16 -32769)))
(check-exn exn:fail? (lambda () (encode-int16 32768)))

(check-equal? (encode-uint16 0) (bytes #x00 #x00))
(check-equal? (encode-uint16 65535) (bytes #xFF #xFF))
(check-exn exn:fail? (lambda () (encode-uint16 -1)))
(check-exn exn:fail? (lambda () (encode-uint16 65536)))

(check-equal? (encode-int32 -2147483648) (bytes #x00 #x00 #x00 #x80))
(check-equal? (encode-int32 2147483647) (bytes #xFF #xFF #xFF #x7F))
(check-exn exn:fail? (lambda () (encode-int32 -2147483649)))
(check-exn exn:fail? (lambda () (encode-int32 2147483648)))

(check-equal? (encode-uint32 4294967295) (bytes #xFF #xFF #xFF #xFF))
(check-exn exn:fail? (lambda () (encode-uint32 4294967296)))

(check-equal? (encode-int64 -9223372036854775808)
              (bytes #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x80))
(check-equal? (encode-int64 9223372036854775807)
              (bytes #xFF #xFF #xFF #xFF #xFF #xFF #xFF #x7F))
(check-exn exn:fail? (lambda () (encode-int64 9223372036854775808)))

;; ---------------------------------------------------------------------------
;; InlineI / InlineI8 instruction operands at the int32 / int64 limits
(check-equal? (encode-instruction 'ldc.i4 -2147483648) (bytes #x20 #x00 #x00 #x00 #x80))
(check-equal? (encode-instruction 'ldc.i4 2147483647) (bytes #x20 #xFF #xFF #xFF #x7F))
(fail-encoding 'ldc.i4 -2147483649)
(check-equal? (encode-instruction 'ldc.i8 -9223372036854775808)
              (bytes #x21 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x80))
(check-equal? (encode-instruction 'ldc.i8 9223372036854775807)
              (bytes #x21 #xFF #xFF #xFF #xFF #xFF #xFF #xFF #x7F))
(fail-encoding 'ldc.i8 9223372036854775808)

;; ShortInlineI for unaligned. and no. is an unsigned byte (0..255)
(check-equal? (encode-instruction 'unaligned. 0) (bytes #xFE #x12 #x00))
(check-equal? (encode-instruction 'unaligned. 255) (bytes #xFE #x12 #xFF))
(fail-encoding 'unaligned. 256)
(fail-encoding 'unaligned. -1)
(check-equal? (encode-instruction 'no. 255) (bytes #xFE #x19 #xFF))
(fail-encoding 'no. 256)

;; ShortInlineVar (uint8) and InlineVar (uint16) at their limits
(check-equal? (encode-instruction 'ldarg.s 0) (bytes #x0E #x00))
(fail-encoding 'ldarg.s -1)
(check-equal? (encode-instruction 'ldarg 0) (bytes #xFE #x09 #x00 #x00))
(check-equal? (encode-instruction 'ldarg 65535) (bytes #xFE #x09 #xFF #xFF))
(fail-encoding 'ldarg -1)

;; Short branch displacement: int8 limits, and each side just outside them
(check-equal? (encode-instruction 'br.s 127) (bytes #x2B #x7F))
(check-equal? (encode-instruction 'br.s -128) (bytes #x2B #x80))
(fail-encoding 'br.s 128)
(fail-encoding 'br.s -129)

;; Long branch displacement: int32 limits
(check-equal? (encode-instruction 'br -129) (bytes #x38 #x7F #xFF #xFF #xFF))
(check-equal? (encode-instruction 'br -2147483648) (bytes #x38 #x00 #x00 #x00 #x80))

;; Tokens: the row index fills the low three bytes, so the maximum row is 0xFFFFFF.
(check-equal? (encode-instruction 'call #x0AFFFFFF) (bytes #x28 #xFF #xFF #xFF #x0A))
(fail-encoding 'call #x0B000001)     ; table 0x0B is not a method table

;; ---------------------------------------------------------------------------
;; ldc.i4 selector (encode-ldc-i4) at every macro boundary
(check-equal? (encode-ldc-i4 -2147483648) (bytes #x20 #x00 #x00 #x00 #x80))
(check-equal? (encode-ldc-i4 -129) (bytes #x20 #x7F #xFF #xFF #xFF))  ; out of int8 range
(check-equal? (encode-ldc-i4 -128) (bytes #x1F #x80))                 ; int8 minimum
(check-equal? (encode-ldc-i4 -2) (bytes #x1F #xFE))                   ; -2 fits int8, so ldc.i4.s
(check-equal? (encode-ldc-i4 -1) (bytes #x15))                        ; ldc.i4.m1
(check-equal? (encode-ldc-i4 0) (bytes #x16))                         ; ldc.i4.0
(check-equal? (encode-ldc-i4 8) (bytes #x1E))                         ; ldc.i4.8
(check-equal? (encode-ldc-i4 9) (bytes #x1F #x09))                    ; first ldc.i4.s
(check-equal? (encode-ldc-i4 127) (bytes #x1F #x7F))                  ; int8 maximum
(check-equal? (encode-ldc-i4 128) (bytes #x20 #x80 #x00 #x00 #x00))   ; first ldc.i4
(check-equal? (encode-ldc-i4 2147483647) (bytes #x20 #xFF #xFF #xFF #x7F))
(check-exn exn:fail? (lambda () (encode-ldc-i4 2147483648)))
(check-exn exn:fail? (lambda () (encode-ldc-i4 -2147483649)))

;; ---------------------------------------------------------------------------
;; Variable-access selectors (encode-var-access) at the 0-3 / 4 / 255 / 256
;; boundaries. Read/write locals and args have 1-byte forms for 0..3 (ldarg.0-3,
;; ldloc.0-3, stloc.0-3). ldarga, ldloca and starg have no such forms, so they
;; start at the .s form. The .s form takes a uint8; past 255 the long form
;; takes a uint16 after the FE prefix.
(check-equal? (encode-var-access 'ldarg 0) (bytes #x02))
(check-equal? (encode-var-access 'ldarg 1) (bytes #x03))
(check-equal? (encode-var-access 'ldarg 2) (bytes #x04))
(check-equal? (encode-var-access 'ldarg 3) (bytes #x05))
(check-equal? (encode-var-access 'ldarg 4) (bytes #x0E #x04))
(check-equal? (encode-var-access 'ldarg 255) (bytes #x0E #xFF))
(check-equal? (encode-var-access 'ldarg 256) (bytes #xFE #x09 #x00 #x01))
(check-equal? (encode-var-access 'ldarg 65535) (bytes #xFE #x09 #xFF #xFF))
(check-exn exn:fail? (lambda () (encode-var-access 'ldarg 65536)))
(check-exn exn:fail? (lambda () (encode-var-access 'ldarg -1)))

(check-equal? (encode-var-access 'ldloc 0) (bytes #x06))
(check-equal? (encode-var-access 'ldloc 3) (bytes #x09))
(check-equal? (encode-var-access 'ldloc 4) (bytes #x11 #x04))
(check-equal? (encode-var-access 'ldloc 255) (bytes #x11 #xFF))
(check-equal? (encode-var-access 'ldloc 256) (bytes #xFE #x0C #x00 #x01))

(check-equal? (encode-var-access 'stloc 0) (bytes #x0A))
(check-equal? (encode-var-access 'stloc 3) (bytes #x0D))
(check-equal? (encode-var-access 'stloc 4) (bytes #x13 #x04))
(check-equal? (encode-var-access 'stloc 255) (bytes #x13 #xFF))
(check-equal? (encode-var-access 'stloc 256) (bytes #xFE #x0E #x00 #x01))

(check-equal? (encode-var-access 'ldarga 0) (bytes #x0F #x00))
(check-equal? (encode-var-access 'ldarga 3) (bytes #x0F #x03))
(check-equal? (encode-var-access 'ldarga 4) (bytes #x0F #x04))
(check-equal? (encode-var-access 'ldarga 255) (bytes #x0F #xFF))
(check-equal? (encode-var-access 'ldarga 256) (bytes #xFE #x0A #x00 #x01))

(check-equal? (encode-var-access 'ldloca 0) (bytes #x12 #x00))
(check-equal? (encode-var-access 'ldloca 3) (bytes #x12 #x03))
(check-equal? (encode-var-access 'ldloca 4) (bytes #x12 #x04))
(check-equal? (encode-var-access 'ldloca 255) (bytes #x12 #xFF))
(check-equal? (encode-var-access 'ldloca 256) (bytes #xFE #x0D #x00 #x01))

(check-equal? (encode-var-access 'starg 0) (bytes #x10 #x00))
(check-equal? (encode-var-access 'starg 3) (bytes #x10 #x03))
(check-equal? (encode-var-access 'starg 4) (bytes #x10 #x04))
(check-equal? (encode-var-access 'starg 255) (bytes #x10 #xFF))
(check-equal? (encode-var-access 'starg 256) (bytes #xFE #x0B #x00 #x01))
