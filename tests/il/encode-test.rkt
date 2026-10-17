#lang racket/base
;; Operand encoder tests. Expected bytes are hand-computed from ECMA-335
;; Partition III encodings (little-endian operands, FE prefix for two-byte opcodes).
(require rackunit
         "../../src/il/encode.rkt"
         "../../src/il/opcodes.rkt")

(define (fail-encoding name operand)
  (check-exn exn:fail? (lambda () (encode-instruction name operand))))

;; InlineNone
(check-equal? (encode-instruction 'nop) (bytes #x00))
(check-equal? (encode-instruction 'ceq) (bytes #xFE #x01))
(check-equal? (encode-instruction 'ldarg.0) (bytes #x02))
(fail-encoding 'nop 1)
(fail-encoding 'ceq 0)

;; ShortInlineI (signed int8 for ldc.i4.s; unsigned for unaligned. and no.)
(check-equal? (encode-instruction 'ldc.i4.s -1) (bytes #x1F #xFF))
(check-equal? (encode-instruction 'ldc.i4.s 127) (bytes #x1F #x7F))
(check-equal? (encode-instruction 'ldc.i4.s -128) (bytes #x1F #x80))
(fail-encoding 'ldc.i4.s 128)
(fail-encoding 'ldc.i4.s -129)
(check-equal? (encode-instruction 'unaligned. 4) (bytes #xFE #x12 #x04))
(check-equal? (encode-instruction 'no. #x80) (bytes #xFE #x19 #x80))

;; InlineI, int32 little-endian
(check-equal? (encode-instruction 'ldc.i4 #x12345678) (bytes #x20 #x78 #x56 #x34 #x12))
(check-equal? (encode-instruction 'ldc.i4 -2) (bytes #x20 #xFE #xFF #xFF #xFF))
(fail-encoding 'ldc.i4 #x80000000)

;; InlineI8, int64 little-endian
(check-equal? (encode-instruction 'ldc.i8 #x0102030405060708)
              (bytes #x21 #x08 #x07 #x06 #x05 #x04 #x03 #x02 #x01))

;; ShortInlineR and InlineR, IEEE 754 little-endian
(check-equal? (encode-instruction 'ldc.r4 1.0) (bytes #x22 #x00 #x00 #x80 #x3F))
(check-equal? (encode-instruction 'ldc.r8 1.0)
              (bytes #x23 #x00 #x00 #x00 #x00 #x00 #x00 #xF0 #x3F))

;; ShortInlineVar (uint8) and InlineVar (uint16)
(check-equal? (encode-instruction 'ldarg.s 255) (bytes #x0E #xFF))
(fail-encoding 'ldarg.s 256)
(check-equal? (encode-instruction 'ldarg #x0102) (bytes #xFE #x09 #x02 #x01))
(check-equal? (encode-instruction 'ldloc 65535) (bytes #xFE #x0C #xFF #xFF))
(fail-encoding 'ldloc 65536)

;; Short and long branch displacements
(check-equal? (encode-instruction 'br.s 5) (bytes #x2B #x05))
(check-equal? (encode-instruction 'br.s -2) (bytes #x2B #xFE))
(check-equal? (encode-instruction 'br #x100) (bytes #x38 #x00 #x01 #x00 #x00))

;; InlineSwitch: uint32 count, then int32 offsets
(check-equal? (encode-instruction 'switch '(10 -4))
              (bytes #x45 #x02 #x00 #x00 #x00
                     #x0A #x00 #x00 #x00
                     #xFC #xFF #xFF #xFF))
(check-equal? (encode-instruction 'switch '()) (bytes #x45 #x00 #x00 #x00 #x00))
(check-equal? (encode-switch-table '(1 -1))
              (bytes #x02 #x00 #x00 #x00 #x01 #x00 #x00 #x00 #xFF #xFF #xFF #xFF))

;; Tokens: table id in the high byte, row in the low three bytes
(check-equal? (encode-instruction 'call #x0A000002) (bytes #x28 #x02 #x00 #x00 #x0A))
(check-equal? (encode-instruction 'calli #x11000001) (bytes #x29 #x01 #x00 #x00 #x11))
(check-equal? (encode-instruction 'ldstr #x70000001) (bytes #x72 #x01 #x00 #x00 #x70))
(check-equal? (encode-instruction 'ldtoken #x02000003) (bytes #xD0 #x03 #x00 #x00 #x02))
(check-equal? (encode-instruction 'ldfld #x04000001) (bytes #x7B #x01 #x00 #x00 #x04))
(fail-encoding 'call #x04000001)            ; Field token where a method is needed
(fail-encoding 'ldstr #x01000001)           ; TypeRef token where a string is needed
(fail-encoding 'call #x0A000000)            ; null token
(fail-encoding 'ldtoken #x70000001)         ; string token is not a type/method/field token

;; Operand arity and names
(fail-encoding 'call #f)
(check-exn exn:fail? (lambda () (encode-instruction 'not-an-opcode)))
(check-equal? (find-opcode 'not-an-opcode) #f)

;; Shortest-form selectors
(check-equal? (encode-ldc-i4 -1) (bytes #x15))
(check-equal? (encode-ldc-i4 0) (bytes #x16))
(check-equal? (encode-ldc-i4 8) (bytes #x1E))
(check-equal? (encode-ldc-i4 9) (bytes #x1F #x09))
(check-equal? (encode-ldc-i4 -128) (bytes #x1F #x80))
(check-equal? (encode-ldc-i4 128) (bytes #x20 #x80 #x00 #x00 #x00))

(check-equal? (encode-var-access 'ldarg 0) (bytes #x02))
(check-equal? (encode-var-access 'ldarg 3) (bytes #x05))
(check-equal? (encode-var-access 'ldarg 4) (bytes #x0E #x04))
(check-equal? (encode-var-access 'ldarg 256) (bytes #xFE #x09 #x00 #x01))
(check-equal? (encode-var-access 'ldarga 0) (bytes #x0F #x00))   ; no 0..3 forms for ldarga
(check-equal? (encode-var-access 'starg 5) (bytes #x10 #x05))
(check-equal? (encode-var-access 'ldloc 2) (bytes #x08))
(check-equal? (encode-var-access 'stloc 0) (bytes #x0A))
(check-equal? (encode-var-access 'ldloca 300) (bytes #xFE #x0D #x2C #x01))

;; instruction-length agrees with the bytes produced, for every table entry
(define (sample-operand kind)
  (case kind
    [(InlineNone) #f]
    [(ShortInlineI InlineI InlineI8 ShortInlineVar InlineVar
      ShortInlineBrTarget InlineBrTarget) 0]
    [(ShortInlineR InlineR) 0.0]
    [(InlineMethod) #x0A000001]
    [(InlineField) #x04000001]
    [(InlineType) #x02000001]
    [(InlineTok) #x01000001]
    [(InlineString) #x70000001]
    [(InlineSig) #x11000001]
    [(InlineSwitch) '(0)]
    [else (error 'test "no sample for ~a" kind)]))

(for ([op (in-list opcode-table)])
  (define name (opcode-name op))
  (define operand (sample-operand (opcode-operand op)))
  (define encoded (encode-instruction name operand))
  (check-equal? (bytes-length encoded) (instruction-length name operand)
                (format "length of ~a" name))
  (check-equal? (bytes-length (opcode-bytes op)) (opcode-size op)
                (format "opcode bytes of ~a" name)))

(check-equal? (instruction-length 'switch '(1 2 3)) 17)
(check-equal? (switch-instruction-length 0) 5)
