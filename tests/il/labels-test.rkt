#lang racket/base
;; Label resolution and branch relaxation tests. Expected bytes are worked out by
;; hand from the short/long branch encodings and the displacement rules
;; (relative to the end of the branch; switch offsets relative to the end of the switch).
(require rackunit
         racket/list
         "../../src/il/labels.rkt")

(define (zeros n) (make-bytes n 0))

(define (assemble-code items)
  (assembly-code (assemble-items items)))

(define (nops n) (make-list n 'nop))

;; Forward short branch: br.s over one nop.
;; br at 0 (2 bytes); nop at 2; end at 3; disp = 3 - 2 = 1.
(check-equal? (assemble-code '((br end) nop end: ret))
              (bytes #x2B #x01 #x00 #x2A))

;; Forward relaxation, displacement 127 still fits in int8.
(check-equal? (assemble-code (append '((br end)) (nops 127) '(end: ret)))
              (bytes-append (bytes #x2B #x7F) (zeros 127) (bytes #x2A)))

;; Displacement 128 does not fit: br grows to the 5-byte form.
;; end = 5 + 128 = 133; disp = 133 - 5 = 128.
(check-equal? (assemble-code (append '((br end)) (nops 128) '(end: ret)))
              (bytes-append (bytes #x38 #x80 #x00 #x00 #x00) (zeros 128) (bytes #x2A)))

;; Backward short branch: top at 0; br at 126; disp = 0 - 128 = -128, fits.
(check-equal? (assemble-code (append '(top:) (nops 126) '((br top))))
              (bytes-append (zeros 126) (bytes #x2B #x80)))

;; Backward relaxation: br at 127; disp = 0 - 129 = -129, so it grows to 5 bytes.
;; The branch ends at 132, so disp = 0 - 132 = -132 = 0xFFFFFF7C.
(check-equal? (assemble-code (append '(top:) (nops 127) '((br top))))
              (bytes-append (zeros 127) (bytes #x38 #x7C #xFF #xFF #xFF)))

;; Cascade: promoting X pushes Y's displacement past int8, so both grow.
;; Initially Y = 129 and X = 132. X grows first, then Y, giving Y = 135 and X = 138.
(check-equal? (assemble-code (append '((br Y) (br X))
                                     (nops 125)
                                     '(Y:)
                                     (nops 3)
                                     '(X: ret)))
              (bytes-append (bytes #x38 #x82 #x00 #x00 #x00)
                            (bytes #x38 #x80 #x00 #x00 #x00)
                            (zeros 125)
                            (zeros 3)
                            (bytes #x2A)))

;; leave pairs with leave.s: DE is the short form (opcode table).
(check-equal? (assemble-code '((leave out) out: ret))
              (bytes #xDE #x00 #x2A))

;; The (label name) form is the same as name:.
(check-equal? (assemble-code '((br.s end) (label end) ret))
              (bytes #x2B #x00 #x2A))

;; Switch: offsets are relative to the end of the switch (13 bytes).
;; a = 13, b = 14, so the offsets are 0 and 1.
(check-equal? (assemble-code '((switch a b) a: nop b: ret))
              (bytes #x45 #x02 #x00 #x00 #x00
                     #x00 #x00 #x00 #x00
                     #x01 #x00 #x00 #x00
                     #x00
                     #x2A))

;; A switch targeting its own start: switch at 1, end at 14, targets at 0.
(check-equal? (assemble-code '((nop) top: (nop) (switch top top)))
              (bytes-append (bytes #x00 #x00)
                            (bytes #x45 #x02 #x00 #x00 #x00)
                            (bytes #xF2 #xFF #xFF #xFF #xF2 #xFF #xFF #xFF)))

;; Label offsets come back in definition order.
(let ([asm (assemble-items '(a: (nop) (br b) b: ret))])
  (check-equal? (assembly-labels asm) '((a . 0) (b . 3)))
  (check-equal? (assembly-label-offset asm 'b) 3))

;; Forced short branch (X.s) must fit; it is never promoted.
(check-equal? (assemble-code (append '((br.s end)) (nops 127) '(end: ret)))
              (bytes-append (bytes #x2B #x7F) (zeros 127) (bytes #x2A)))
(check-exn exn:fail?
           (lambda () (assemble-items (append '((br.s end)) (nops 128) '(end: ret)))))

;; Errors: undefined label, duplicate label, bad target, unknown opcode.
(check-exn exn:fail? (lambda () (assemble-items '((br nowhere) ret))))
(check-exn exn:fail? (lambda () (assemble-items '(x: nop x: ret))))
(check-exn exn:fail? (lambda () (assemble-items '((br 5) ret))))
(check-exn exn:fail? (lambda () (assemble-items '((frob x)))))

;; Assembly is deterministic: same input, same output.
(check-equal? (assemble-code (append '((br end)) (nops 200) '(end: ret)))
              (assemble-code (append '((br end)) (nops 200) '(end: ret))))
