#lang racket/base
; Tests for the insertion-ordered metadata heaps (ECMA-335 II.24.2).
(require rackunit
         "../../src/cli/heaps.rkt")

(define (us-entry s)
  (define h (make-us-heap))
  (heap-add! h s)
  (subbytes (heap-serialise h) 1))

(define (blob-entry b)
  (define h (make-blob-heap))
  (heap-add! h b)
  (subbytes (heap-serialise h) 1))

; ---------------------------------------------------------------------------
; empty entries and dedup

(test-case "empty entry is index 0 in #Strings and #Blob"
  (check-equal? (heap-serialise (make-strings-heap)) (bytes 0))
  (check-equal? (heap-serialise (make-blob-heap)) (bytes 0))
  (check-equal? (heap-serialise (make-guid-heap)) #"")
  (let ([s (make-strings-heap)] [b (make-blob-heap)])
    (check-equal? (heap-add! s "") 0)
    (check-equal? (heap-add! b #"") 0)
    (check-equal? (heap-serialise s) (bytes 0))
    (check-equal? (heap-serialise b) (bytes 0))))

(test-case "#US offset 0 is never handed out, so \"\" is a real entry"
  (check-equal? (heap-serialise (make-us-heap)) (bytes 0))
  (define u (make-us-heap))
  (check-equal? (heap-add! u "") 1)
  (check-equal? (heap-add! u "") 1)
  (check-equal? (heap-add! u "a") 3)
  (check-equal? (heap-serialise u) (bytes 0 1 0 3 #x61 0 0)))

(test-case "adding an existing value returns its index"
  (define h (make-strings-heap))
  (check-equal? (heap-add! h "abc") 1)
  (check-equal? (heap-add! h "abc") 1)
  (check-equal? (heap-add! h "x") 5)
  (check-equal? (heap-add! h "x") 5)
  (check-equal? (heap-serialise h) (bytes 0 #x61 #x62 #x63 0 #x78 0)))

(test-case "blob dedup and offsets"
  (define h (make-blob-heap))
  (check-equal? (heap-add! h #"ab") 1)
  (check-equal? (heap-add! h #"ab") 1)
  (check-equal? (heap-add! h #"") 0)
  (check-equal? (heap-add! h #"c") 4)
  (check-equal? (heap-serialise h) (bytes 0 2 #x61 #x62 1 #x63)))

(test-case "#Strings is UTF-8 with a NUL terminator"
  (define h (make-strings-heap))
  (check-equal? (heap-add! h "\u00E9") 1)
  (check-equal? (heap-serialise h) (bytes 0 #xC3 #xA9 0))
  (check-exn exn:fail? (lambda () (heap-add! h "a\u0000b"))))

; ---------------------------------------------------------------------------
; insertion order

(test-case "output follows insertion order, not value order"
  (define a (make-strings-heap))
  (heap-add! a "a")
  (heap-add! a "b")
  (define b (make-strings-heap))
  (heap-add! b "b")
  (heap-add! b "a")
  (check-equal? (heap-serialise a) (bytes 0 #x61 0 #x62 0))
  (check-equal? (heap-serialise b) (bytes 0 #x62 0 #x61 0))
  (check-not-equal? (heap-serialise a) (heap-serialise b)))

(test-case "#US insertion order and indexes"
  (define a (make-us-heap))
  (check-equal? (heap-add! a "a") 1)
  (check-equal? (heap-add! a "b") 5)
  (check-equal? (heap-serialise a) (bytes 0 3 #x61 0 0 3 #x62 0 0))
  (define b (make-us-heap))
  (check-equal? (heap-add! b "b") 1)
  (check-equal? (heap-add! b "a") 5)
  (check-equal? (heap-serialise b) (bytes 0 3 #x62 0 0 3 #x61 0 0)))

(test-case "same insertion sequence gives identical bytes"
  (define (build)
    (define h (make-strings-heap))
    (for ([i (in-range 50)])
      (heap-add! h (format "name~a" (modulo (* i 7) 50))))
    (heap-serialise h))
  (check-equal? (build) (build)))

; ---------------------------------------------------------------------------
; #US exact bytes and flag rule (II.24.2.4)

(test-case "#US exact bytes with non-ASCII and control characters"
  (define h (make-us-heap))
  (check-equal? (heap-add! h "a\u00E9\t\u0001\u2603") 1)
  (check-equal? (heap-serialise h)
                (bytes 0 #x0B #x61 #x00 #xE9 #x00 #x09 #x00 #x01 #x00 #x03 #x26 #x01)))

(test-case "#US exact bytes for a plain string (flag 0)"
  (check-equal? (us-entry "\t") (bytes 3 #x09 0 0)))

(test-case "#US flag byte follows II.24.2.4"
  (define (flag s)
    (define e (us-entry s))
    (bytes-ref e (sub1 (bytes-length e))))
  ; flagged: low byte in 0x01-0x08, 0x0E-0x1F, 0x27, 0x2D, or any unit >= 0x7F
  (for ([c (list #\u0001 #\u0008 #\u000E #\u001F #\u0027 #\u002D #\u007F #\u00E9 #\u2603)])
    (check-equal? (flag (string c)) 1 (format "U+~a should set the flag" (number->string (char->integer c) 16))))
  ; not flagged
  (for ([c (list #\u0009 #\u000A #\u000D #\u0020 #\u0021 #\u007E #\u0041)])
    (check-equal? (flag (string c)) 0 (format "U+~a should not set the flag" (number->string (char->integer c) 16))))
  ; U+0000 is flagged (matches ilasm; the spec list does not name it)
  (check-equal? (flag "\u0000") 1)
  ; supplementary characters are two surrogate units, both >= 0x7F
  (check-equal? (flag "\U1F600") 1))

(test-case "#US surrogate pair encoding"
  (check-equal? (us-entry "\U1F600") (bytes 5 #x3D #xD8 #x00 #xDE 1)))

(test-case "#US exact entry for a control character"
  (check-equal? (us-entry "\u0027") (bytes 3 #x27 0 1)))

; ---------------------------------------------------------------------------
; compressed length boundaries (II.23.2)

(test-case "#US compressed length boundaries"
  ; 63 chars: UTF-16 byte count + 1 = 127 = 0x7F, one byte
  (let ([e (us-entry (make-string 63 #\a))])
    (check-equal? (bytes-ref e 0) #x7F)
    (check-equal? (bytes-length e) (+ 1 126 1)))
  ; 64 chars: 129 = 0x81, two bytes
  (let ([e (us-entry (make-string 64 #\a))])
    (check-equal? (subbytes e 0 2) (bytes #x80 #x81))
    (check-equal? (bytes-length e) (+ 2 128 1)))
  ; 8191 chars: 16383 = 0x3FFF, two bytes
  (let ([e (us-entry (make-string 8191 #\a))])
    (check-equal? (subbytes e 0 2) (bytes #xBF #xFF))
    (check-equal? (bytes-length e) (+ 2 16382 1)))
  ; 8192 chars: 16385 = 0x4001, four bytes
  (let ([e (us-entry (make-string 8192 #\a))])
    (check-equal? (subbytes e 0 4) (bytes #xC0 #x00 #x40 #x01))
    (check-equal? (bytes-length e) (+ 4 16384 1))))

(test-case "#Blob compressed length boundaries"
  (let ([e (blob-entry (make-bytes 127 7))])
    (check-equal? (bytes-ref e 0) #x7F)
    (check-equal? (bytes-length e) (+ 1 127)))
  (let ([e (blob-entry (make-bytes 128 7))])
    (check-equal? (subbytes e 0 2) (bytes #x80 #x80))
    (check-equal? (bytes-length e) (+ 2 128)))
  (let ([e (blob-entry (make-bytes 16383 7))])
    (check-equal? (subbytes e 0 2) (bytes #xBF #xFF))
    (check-equal? (bytes-length e) (+ 2 16383)))
  (let ([e (blob-entry (make-bytes 16384 7))])
    (check-equal? (subbytes e 0 4) (bytes #xC0 #x00 #x40 #x00))
    (check-equal? (bytes-length e) (+ 4 16384))))

; ---------------------------------------------------------------------------
; #GUID (II.24.2.5)

(test-case "GUID indexes are 1-based and deduplicated"
  (define g1 (make-bytes 16 1))
  (define g2 (make-bytes 16 2))
  (define h (make-guid-heap))
  (check-equal? (heap-add! h g1) 1)
  (check-equal? (heap-add! h g2) 2)
  (check-equal? (heap-add! h g1) 1)
  (check-equal? (heap-serialise h) (bytes-append g1 g2)))

(test-case "GUID entries must be 16 bytes"
  (check-exn exn:fail? (lambda () (heap-add! (make-guid-heap) (make-bytes 15 0))))
  (check-exn exn:fail? (lambda () (heap-add! (make-guid-heap) (make-bytes 17 0)))))
