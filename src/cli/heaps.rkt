#lang racket/base
; Metadata heaps (ECMA-335 II.24.2). Each heap hands out the index of a value,
; deduplicating repeats, and serialises entries in insertion order. A hash is used
; only for lookup, so output never depends on hash iteration order.
(require "../private/binary.rkt")
(provide make-strings-heap make-us-heap make-blob-heap make-guid-heap
         heap-add! heap-serialise)

; encode:        value -> bytes written for one entry
; key-of:        value -> immutable key used for deduplication
; offset->index: byte offset of an entry -> index handed back to the caller
; table:         key -> index
; chunks:        encoded entries, newest first
; size:          total bytes written so far
(struct heap (encode key-of offset->index table [chunks #:mutable] [size #:mutable]))

; byte heaps start with an empty entry at offset 0 (index 0 is the empty value)
(define (make-byte-heap encode key-of empty)
  (define table (make-hash))
  (hash-set! table (key-of empty) 0)
  (heap encode key-of values table (list (bytes 0)) 1))

(define (heap-add! h v)
  (define key ((heap-key-of h) v))
  (or (hash-ref (heap-table h) key #f)
      (let* ([bs ((heap-encode h) v)]
             [offset (heap-size h)]
             [index ((heap-offset->index h) offset)])
        (hash-set! (heap-table h) key index)
        (set-heap-chunks! h (cons bs (heap-chunks h)))
        (set-heap-size! h (+ offset (bytes-length bs)))
        index)))

(define (heap-serialise h)
  (apply bytes-append (reverse (heap-chunks h))))

; ---------------------------------------------------------------------------
; #Strings (II.24.2.3): UTF-8, NUL-terminated. A NUL inside a string cannot be stored.

(define (encode-utf8 s)
  (when (for/or ([c (in-string s)]) (char=? c #\nul))
    (error 'make-strings-heap "string contains NUL, which #Strings cannot represent: ~s" s))
  (bytes-append (string->bytes/utf-8 s) (bytes 0)))

(define (make-strings-heap)
  (make-byte-heap encode-utf8 string->immutable-string ""))

; ---------------------------------------------------------------------------
; #US (II.24.2.4): compressed length (UTF-16 byte count + 1), UTF-16LE code units,
; then one flag byte.

; UTF-16 code units for one code point
(define (code-point->utf16-units n)
  (if (< n #x10000)
      (list n)
      (let ([m (- n #x10000)])
        (list (+ #xD800 (arithmetic-shift m -10))
              (+ #xDC00 (bitwise-and m #x3FF))))))

(define (string->utf16-units s)
  (for*/list ([c (in-string s)]
              [u (in-list (code-point->utf16-units (char->integer c)))])
    u))

; Flag rule from II.24.2.4: 1 if any unit has a bit set above the low 7 bits (>= 0x7F),
; or its low byte is 0x01-0x08, 0x0E-0x1F, 0x27 or 0x2D. U+0000 is also flagged,
; matching ilasm (the spec list does not mention it).
(define (special-unit? u)
  (or (>= u #x7F)
      (= u 0)
      (<= 1 u 8)
      (<= #x0E u #x1F)
      (= u #x27)
      (= u #x2D)))

(define (encode-us s)
  (define units (string->utf16-units s))
  (define body (apply bytes-append (for/list ([u (in-list units)]) (le u 2))))
  (bytes-append (compress-unsigned (add1 (bytes-length body)))
                body
                (bytes (if (ormap special-unit? units) 1 0))))

(define (make-us-heap)
  (make-byte-heap encode-us string->immutable-string ""))

; ---------------------------------------------------------------------------
; #Blob (II.24.2.4): compressed length, then the bytes.

(define (encode-blob b)
  (bytes-append (compress-unsigned (bytes-length b)) b))

(define (make-blob-heap)
  (make-byte-heap encode-blob bytes->immutable-bytes #""))

; ---------------------------------------------------------------------------
; #GUID (II.24.2.5): 16 bytes per entry. Indexes are 1-based; 0 means no GUID.

(define (encode-guid g)
  (unless (and (bytes? g) (= (bytes-length g) 16))
    (error 'make-guid-heap "a GUID must be exactly 16 bytes: ~e" g))
  g)

(define (make-guid-heap)
  (heap encode-guid
        bytes->immutable-bytes
        (lambda (offset) (add1 (quotient offset 16)))
        (make-hash)
        '()
        0))
