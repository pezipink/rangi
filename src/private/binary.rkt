#lang racket/base
; Little-endian byte helpers shared by the CLI and PE writers.
(provide le align pad-to)

; k-byte little-endian encoding of n
(define (le n k)
  (unless (and (exact-nonnegative-integer? n) (< n (expt 2 (* 8 k))))
    (error 'rangi "value ~a does not fit in ~a bytes" n k))
  (define b (make-bytes k 0))
  (for ([i (in-range k)])
    (bytes-set! b i (bitwise-and (arithmetic-shift n (* -8 i)) #xFF)))
  b)

; smallest multiple of a that is >= n
(define (align n a) (* a (quotient (+ n a -1) a)))

; zero-pad bs so its length is a multiple of n
(define (pad-to bs n)
  (bytes-append bs (make-bytes (- (align (bytes-length bs) n) (bytes-length bs)) 0)))
