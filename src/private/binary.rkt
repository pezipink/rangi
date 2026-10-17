#lang racket/base
; Byte helpers shared by the CLI and PE readers and writers. One source of truth for
; little-endian integers, alignment, and the compressed integer format (ECMA-335 II.23.2).
(provide le
         write-u8-le write-u16-le write-u32-le write-u64-le
         bytes->uint-le read-uint-le read-u8-le read-u16-le read-u32-le read-u64-le
         align-up pad-to
         compress-unsigned decompress-unsigned)

; ---------------------------------------------------------------------------
; little-endian writers

; k-byte little-endian encoding of n
(define (le n k)
  (unless (and (exact-nonnegative-integer? n) (< n (expt 2 (* 8 k))))
    (error 'rangi "value ~a does not fit in ~a bytes" n k))
  (define b (make-bytes k 0))
  (for ([i (in-range k)])
    (bytes-set! b i (bitwise-and (arithmetic-shift n (* -8 i)) #xFF)))
  b)

(define (write-u8-le n) (le n 1))
(define (write-u16-le n) (le n 2))
(define (write-u32-le n) (le n 4))
(define (write-u64-le n) (le n 8))

; ---------------------------------------------------------------------------
; little-endian readers

; unsigned little-endian value of a byte string of any length
(define (bytes->uint-le bs)
  (define n (bytes-length bs))
  (if (memv n '(1 2 4 8))
      (integer-bytes->integer bs #f #f)
      (for/fold ([acc 0]) ([i (in-range (sub1 n) -1 -1)])
        (+ (* acc 256) (bytes-ref bs i)))))

; read size bytes from port as an unsigned little-endian value
(define (read-uint-le size port) (bytes->uint-le (read-bytes size port)))

(define (read-u8-le port) (read-uint-le 1 port))
(define (read-u16-le port) (read-uint-le 2 port))
(define (read-u32-le port) (read-uint-le 4 port))
(define (read-u64-le port) (read-uint-le 8 port))

; ---------------------------------------------------------------------------
; alignment

; smallest multiple of a that is >= n
(define (align-up n a) (* a (quotient (+ n a -1) a)))

; zero-pad bs so its length is a multiple of n
(define (pad-to bs n)
  (bytes-append bs (make-bytes (- (align-up (bytes-length bs) n) (bytes-length bs)) 0)))

; ---------------------------------------------------------------------------
; compressed unsigned integers (II.23.2)
;   0xxxxxxx                  7-bit value, 1 byte
;   10xxxxxx xxxxxxxx         14-bit value, 2 bytes, big-endian
;   110xxxxx xxxxxxxx x3      29-bit value, 4 bytes, big-endian

(define (compress-unsigned n)
  (cond
    [(< n #x80) (bytes n)]
    [(< n #x4000) (bytes (bitwise-ior #x80 (arithmetic-shift n -8)) (bitwise-and n #xFF))]
    [(< n #x20000000)
     (bytes (bitwise-ior #xC0 (arithmetic-shift n -24))
            (bitwise-and (arithmetic-shift n -16) #xFF)
            (bitwise-and (arithmetic-shift n -8) #xFF)
            (bitwise-and n #xFF))]
    [else (error 'rangi "value ~a is too large for a compressed integer" n)]))

; read one compressed unsigned integer from port
(define (decompress-unsigned port)
  (define first (read-byte port))
  (cond
    [(equal? (bitwise-and first #xC0) #xC0)
     (define second (read-byte port))
     (define third (read-byte port))
     (define fourth (read-byte port))
     (bitwise-ior (arithmetic-shift (bitwise-and first #x1F) 24)
                  (arithmetic-shift second 16)
                  (arithmetic-shift third 8)
                  fourth)]
    [(equal? (bitwise-and first #x80) #x80)
     (define second (read-byte port))
     (bitwise-ior (arithmetic-shift (bitwise-and first #x3F) 8) second)]
    [else first]))
