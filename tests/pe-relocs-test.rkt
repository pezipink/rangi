#lang racket/base
; Unit tests for the base relocation table encoding (PE/COFF section 5.6, data directory 5)
(require rackunit
         racket/list
         "../src/private/binary.rkt"
         "../src/pe/layout.rkt"
         "../src/pe/relocs.rkt")

(define params (image-params 'pe32 #x14C #x102 3 #x8540 #x400000 #x2000 #x200))

(define (image-of . chunks)
  (layout-image params (list (section ".text" #x60000020 chunks))))

; little-endian unsigned integer from bytes
(define (read-le bs start n)
  (for/fold ([acc 0]) ([i (in-range n)])
    (+ acc (arithmetic-shift (bytes-ref bs (+ start i)) (* 8 i)))))

; split a base relocation table into (list page block-size entries) per block;
; entries are (cons type offset) pairs
(define (parse-blocks bs)
  (let loop ([pos 0] [acc '()])
    (cond
      [(>= pos (bytes-length bs)) (reverse acc)]
      [else
       (define page (read-le bs pos 4))
       (define size (read-le bs (+ pos 4) 4))
       (define entries
         (for/list ([e (in-range (quotient (- size 8) 2))])
           (define w (read-le bs (+ pos 8 (* 2 e)) 2))
           (cons (arithmetic-shift w -12) (bitwise-and w #xFFF))))
       (loop (+ pos size) (cons (list page size entries) acc))])))

(define (highlow offset) (+ (arithmetic-shift 3 12) offset))

(test-case "two entries fill the body exactly, so the block needs no padding"
  (define img (image-of (chunk 'a 4 (make-bytes 8 0) (list (fixup 0 'va32 'b) (fixup 4 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define a-rva (placed-rva img 'a))
  (check-equal? (chunk-bytes (base-relocation-chunk img))
                (bytes-append (le a-rva 4) (le 12 4) (le (highlow 0) 2) (le (highlow 4) 2))))

(test-case "three entries are padded with an ABSOLUTE entry to a 4-byte body"
  (define img (image-of (chunk 'a 4 (make-bytes 12 0)
                               (list (fixup 0 'va32 'b) (fixup 4 'va32 'b) (fixup 8 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define blocks (parse-blocks (chunk-bytes (base-relocation-chunk img))))
  (check-equal? (length blocks) 1)
  (define blk (car blocks))
  (check-equal? (second blk) 16)
  (check-equal? (third blk) (list (cons 3 0) (cons 3 4) (cons 3 8) (cons 0 0))))

(test-case "sites on two pages give two blocks, each with its own page RVA"
  ; a is 0x1800 bytes at RVA 0x2000; b follows it at 0x3800
  (define img (image-of (chunk 'a 4 (make-bytes #x1800 0)
                               (list (fixup 0 'va32 'b) (fixup #xFFC 'va32 'b) (fixup #x1000 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define a-rva (placed-rva img 'a))
  (check-equal? a-rva #x2000)
  (define blocks (parse-blocks (chunk-bytes (base-relocation-chunk img))))
  (check-equal? blocks
                (list (list #x2000 12 (list (cons 3 0) (cons 3 #xFFC)))
                      (list #x3000 12 (list (cons 3 0) (cons 0 0))))))

(test-case "a site at the last dword of a page is encoded with page offset 0xFFC"
  (define img (image-of (chunk 'a 4 (make-bytes #x1000 0) (list (fixup #xFFC 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (check-equal? (chunk-bytes (base-relocation-chunk img))
                (bytes-append (le #x2000 4) (le 12 4) (le (highlow #xFFC) 2) (le 0 2))))

(test-case "sites in a second section give a block for that section's page"
  (define img
    (layout-image params
                  (list (section ".text" #x60000020
                                 (list (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'va32 'b)))
                                       (chunk 'b 4 (make-bytes 4 0) '())))
                        (section ".data" #xC0000040
                                 (list (chunk 'c 4 (make-bytes 4 0) (list (fixup 0 'va32 'a))))))))
  (check-equal? (placed-rva img 'c) #x4000)
  (define blocks (parse-blocks (chunk-bytes (base-relocation-chunk img))))
  (check-equal? blocks
                (list (list #x2000 12 (list (cons 3 0) (cons 0 0)))
                      (list #x4000 12 (list (cons 3 0) (cons 0 0))))))

(test-case "every block has a page-aligned RVA and a size that is a multiple of 4"
  (define img (image-of (chunk 'a 4 (make-bytes #x2008 0)
                               (list (fixup 0 'va32 'b) (fixup #x7FC 'va32 'b)
                                     (fixup #xFFC 'va32 'b) (fixup #x1000 'va32 'b)
                                     (fixup #x2000 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define bs (chunk-bytes (base-relocation-chunk img)))
  (define blocks (parse-blocks bs))
  (for ([blk (in-list blocks)])
    (check-equal? (remainder (first blk) #x1000) 0)
    (check-equal? (remainder (second blk) 4) 0))
  (check-equal? (apply + (map second blocks)) (bytes-length bs))
  (check-equal? (map first blocks) '(#x2000 #x3000 #x4000)))

(test-case "the table is itself dword-aligned as a section"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'va32 'a)))))
  (define rel (base-relocation-chunk img))
  (check-equal? (chunk-align rel) 4)
  (check-equal? (remainder (bytes-length (chunk-bytes rel)) 4) 0))
