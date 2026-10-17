#lang racket/base
;; Branch relaxation at the int8 limit. A short branch's displacement is an int8
;; measured from the end of the branch instruction, so it must lie in -128..127.
;; Expected bytes are derived by hand from the short and long encodings in
;; src/il/opcodes.rkt and the relaxation rules in labels.rkt.
(require rackunit
         racket/list
         "../../src/il/labels.rkt")

(define (zeros n) (make-bytes n 0))
(define (nops n) (make-list n 'nop))
(define (assemble-code items) (assembly-code (assemble-items items)))

;; Short and long opcode bytes for each branch that has both forms.
(define branch-forms
  '((br      #x2B #x38)
    (brtrue  #x2D #x3A)
    (beq     #x2E #x3B)
    (bne.un  #x33 #x40)
    (leave   #xDE #xDD)))

;; Each form at the int8 limit, for every branch opcode with a short form.
;; Forward: the branch is 2 bytes (short), so a target 127 bytes after its end
;; is the last short displacement. Backward: the target is at offset 0, and the
;; branch is placed so its end is 128 bytes from the target (-128) or 129 (-129).
(for ([form (in-list branch-forms)])
  (define name (car form))
  (define short (cadr form))
  (define long (caddr form))
  (define (fwd n) (append (list (list name 'end)) (nops n) '(end: ret)))
  (define (bwd n) (append '(top:) (nops n) (list (list name 'top))))
  (define ret #x2A)

  ;; Forward 127: stays short. Displacement 127 = 0x7F.
  (check-equal? (assemble-code (fwd 127))
                (bytes-append (bytes short #x7F) (zeros 127) (bytes ret))
                (format "~a forward 127 should stay short" name))

  ;; Forward 128: widened. Long end = 5 + 128 = 133, so displacement 128 = 0x80.
  (check-equal? (assemble-code (fwd 128))
                (bytes-append (bytes long #x80 #x00 #x00 #x00) (zeros 128) (bytes ret))
                (format "~a forward 128 should widen" name))

  ;; Backward -128: stays short. The branch ends at 128, so displacement = -128 = 0x80.
  (check-equal? (assemble-code (bwd 126))
                (bytes-append (zeros 126) (bytes short #x80))
                (format "~a backward -128 should stay short" name))

  ;; Backward -129: widened. The branch sits at 127 and ends at 132, so
  ;; displacement = -132 = 0xFFFFFF7C.
  (check-equal? (assemble-code (bwd 127))
                (bytes-append (zeros 127) (bytes long #x7C #xFF #xFF #xFF))
                (format "~a backward -129 should widen" name)))

;; ---------------------------------------------------------------------------
;; Cascades: widening one branch pushes another over the limit.

;; Backward branch pushed past -128 by a forward widening that sits between the
;; target and the branch.
;;   pass 1: br X (0, short) widens (disp 256); br top (126) is still -128, so it fits.
;;   pass 2: br X is 5 bytes, so br top (129) now has disp -131 and widens.
;;   pass 3: no short branch fails, so the loop stops.
;; Final: br X at 0 (long) with disp 259; br top at 129 (long) with disp -134.
(check-equal? (assemble-code (append '(top:) '((br X)) (nops 124) '((br top)) (nops 130) '(X: ret)))
              (bytes-append (bytes #x38 #x03 #x01 #x00 #x00)
                            (zeros 124)
                            (bytes #x38 #x7A #xFF #xFF #xFF)
                            (zeros 130)
                            (bytes #x2A)))

;; Forward branch B stays short after a cascade, when its final displacement is
;; exactly 127. B at 0 targets Z. A (at 2) is widened because it targets far
;; W, which adds 3 bytes between B and Z.
;;   pass 1: B disp 124 (fits); A widens.
;;   pass 2: Z = 129, so B disp = 127 and it stays short.
(check-equal? (assemble-code (append '((brtrue Z)) '((br W)) (nops 122) '(Z:) (nops 300) '(W: ret)))
              (bytes-append (bytes #x2D #x7F)
                            (bytes #x38 #xA6 #x01 #x00 #x00)
                            (zeros 122)
                            (zeros 300)
                            (bytes #x2A)))

;; Same shape with one more nop, so B's displacement reaches exactly 128 and it
;; widens.
;;   pass 1: B disp 125 (fits); A widens.
;;   pass 2: Z = 130, so B disp = 128 and it widens.
;;   pass 3: no short branch fails, so the loop stops.
;; Final: B long at 0 with disp 128; A long at 5 with disp 423.
(check-equal? (assemble-code (append '((brtrue Z)) '((br W)) (nops 123) '(Z:) (nops 300) '(W: ret)))
              (bytes-append (bytes #x3A #x80 #x00 #x00 #x00)
                            (bytes #x38 #xA7 #x01 #x00 #x00)
                            (zeros 123)
                            (zeros 300)
                            (bytes #x2A)))

;; Four-pass cascade. Each widening pushes the next branch over the limit:
;;   D (br Q at 0) reaches Q at 128. Its span covers the padding and B.
;;   B (brtrue Z at 126) reaches Z past A.
;;   A (br W at 128) is far from W, so it widens first.
;; Layout after pass 1: A widens, so Z moves to 254 and B's disp is 126 (fits).
;; Pass 2: B's disp becomes 129, so B widens. Q moves to 131.
;; Pass 3: D's disp becomes 129, so D widens. The loop then stops.
;; Final: D long at 0 (disp 129), B long at 129 (disp 129), A long at 134 (disp 134).
(check-equal? (assemble-code (append '((br Q))
                                     (nops 124)
                                     '((brtrue Z))
                                     '(Q:)
                                     '((br W))
                                     (nops 124)
                                     '(Z:)
                                     (nops 10)
                                     '(W: ret)))
              (bytes-append (bytes #x38 #x81 #x00 #x00 #x00)
                            (zeros 124)
                            (bytes #x3A #x81 #x00 #x00 #x00)
                            (bytes #x38 #x86 #x00 #x00 #x00)
                            (zeros 124)
                            (zeros 10)
                            (bytes #x2A)))
