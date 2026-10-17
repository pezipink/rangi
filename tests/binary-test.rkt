#lang racket/base
; Boundary tests for the shared byte helpers in src/private/binary.rkt.
(require rackunit
         "../src/private/binary.rkt")

; ---------------------------------------------------------------------------
; compressed unsigned integers (II.23.2)

(define (compressed n) (compress-unsigned n))
(define (round-trip n)
  (decompress-unsigned (open-input-bytes (compress-unsigned n))))

(test-case "compress-unsigned 1-byte form up to 0x7F"
  (check-equal? (compressed #x00) #"\x00")
  (check-equal? (compressed #x7F) #"\x7F")
  (check-equal? (bytes-length (compressed #x7F)) 1))

(test-case "compress-unsigned 2-byte form starts at 0x80"
  (check-equal? (compressed #x80) #"\x80\x80")
  (check-equal? (compressed #x3FFF) #"\xBF\xFF")
  (check-equal? (bytes-length (compressed #x80)) 2)
  (check-equal? (bytes-length (compressed #x3FFF)) 2))

(test-case "compress-unsigned 4-byte form starts at 0x4000"
  (check-equal? (compressed #x4000) #"\xC0\x00\x40\x00")
  (check-equal? (compressed #x1FFFFFFF) #"\xDF\xFF\xFF\xFF")
  (check-equal? (bytes-length (compressed #x4000)) 4)
  (check-equal? (bytes-length (compressed #x1FFFFFFF)) 4))

(test-case "compress-unsigned rejects values above 0x1FFFFFFF"
  (check-exn exn:fail? (lambda () (compress-unsigned #x20000000)))
  (check-exn exn:fail? (lambda () (compress-unsigned -1))))

(test-case "decompress-unsigned round-trips every boundary"
  (for ([n (in-list '(0 1 #x7E #x7F #x80 #x81 #x3FFE #x3FFF #x4000 #x4001
                      #xFFFF #x10000 #xFFFFFF #x1000000 #x1FFFFFFE #x1FFFFFFF))])
    (check-equal? (round-trip n) n (format "round trip of ~x" n))))

(test-case "decompress-unsigned reads consecutive values from one port"
  (define in (open-input-bytes (bytes-append (compressed #x7F) (compressed #x80)
                                             (compressed #x4000))))
  (check-equal? (decompress-unsigned in) #x7F)
  (check-equal? (decompress-unsigned in) #x80)
  (check-equal? (decompress-unsigned in) #x4000)
  (check-true (eof-object? (read-byte in))))

; ---------------------------------------------------------------------------
; little-endian writers

(test-case "write-u8-le"
  (check-equal? (write-u8-le #xAB) #"\xAB")
  (check-exn exn:fail? (lambda () (write-u8-le 256)))
  (check-exn exn:fail? (lambda () (write-u8-le -1))))

(test-case "write-u16-le"
  (check-equal? (write-u16-le #x1234) #"\x34\x12")
  (check-equal? (write-u16-le #xFFFF) #"\xFF\xFF")
  (check-exn exn:fail? (lambda () (write-u16-le #x10000))))

(test-case "write-u32-le"
  (check-equal? (write-u32-le #x12345678) #"\x78\x56\x34\x12")
  (check-equal? (write-u32-le #xFFFFFFFF) #"\xFF\xFF\xFF\xFF")
  (check-exn exn:fail? (lambda () (write-u32-le #x100000000))))

(test-case "write-u64-le"
  (check-equal? (write-u64-le #x0102030405060708) #"\x08\x07\x06\x05\x04\x03\x02\x01")
  (check-exn exn:fail? (lambda () (write-u64-le (expt 2 64)))))

; ---------------------------------------------------------------------------
; little-endian readers

(test-case "bytes->uint-le for fixed sizes"
  (check-equal? (bytes->uint-le #"\x34\x12") #x1234)
  (check-equal? (bytes->uint-le #"\x78\x56\x34\x12") #x12345678)
  (check-equal? (bytes->uint-le #"\xFF\xFF\xFF\xFF") #xFFFFFFFF))

(test-case "bytes->uint-le for other lengths"
  (check-equal? (bytes->uint-le #"\x01\x02\x03") #x030201)
  (check-equal? (bytes->uint-le #"\x01\x02\x03\x04\x05") #x0504030201)
  (check-equal? (bytes->uint-le #"\x7F") #x7F))

(test-case "read-uint-le and the fixed-width port readers"
  (define in (open-input-bytes #"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A\x0B\x0C\x0D\x0E\x0F"))
  (check-equal? (read-u8-le in) #x01)
  (check-equal? (read-u16-le in) #x0302)
  (check-equal? (read-uint-le 3 in) #x060504)
  (check-equal? (read-u32-le in) #x0A090807)
  (check-equal? (read-u64-le (open-input-bytes #"\x08\x07\x06\x05\x04\x03\x02\x01"))
                #x0102030405060708))

(test-case "write and read round trip"
  (for ([n (in-list '(0 1 #xFF #x100 #xFFFF #x10000 #xFFFFFFFF))])
    (check-equal? (bytes->uint-le (write-u32-le n)) n)))

; ---------------------------------------------------------------------------
; alignment

(test-case "align-up"
  (check-equal? (align-up 0 4) 0)
  (check-equal? (align-up 1 4) 4)
  (check-equal? (align-up 4 4) 4)
  (check-equal? (align-up 5 4) 8)
  (check-equal? (align-up #x200 #x200) #x200)
  (check-equal? (align-up #x201 #x200) #x400))

(test-case "pad-to"
  (check-equal? (pad-to #"abc" 4) #"abc\x00")
  (check-equal? (pad-to #"abcd" 4) #"abcd")
  (check-equal? (pad-to #"" 4) #""))
