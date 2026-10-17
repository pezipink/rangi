#lang racket/base
; Unit tests for the PE fixup model: rva32, va32 and digest fields, and base relocation sites
(require rackunit
         "../src/private/binary.rkt"
         "../src/pe/layout.rkt"
         "../src/pe/relocs.rkt"
         "../src/pe/write.rkt")

(define params (image-params 'pe32 #x14C #x102 3 #x8540 #x400000 #x2000 #x200))

(define (image-of . chunks)
  (layout-image params (list (section ".text" #x60000020 chunks))))

(test-case "rva32 fixup holds the RVA of its target"
  (define img (image-of (chunk 'a 4 (make-bytes 8 0) (list (fixup 4 'rva32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define out (render-chunk img (lookup-placement img 'a)))
  (check-equal? (subbytes out 0 4) (make-bytes 4 0))
  (check-equal? (subbytes out 4 8) (le (placed-rva img 'b) 4)))

(test-case "va32 fixup holds the image base plus the RVA of its target"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'va32 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define out (render-chunk img (lookup-placement img 'a)))
  (check-equal? out (le (+ #x400000 (placed-rva img 'b)) 4)))

(test-case "digest is the first 16 bytes of SHA-256 over its spans, taken after RVA fixups"
  (define img (image-of (chunk 'a 4 (make-bytes 32 1) (list (fixup 0 'rva32 'a)
                                                            (digest 16 (list (cons 0 4) (cons 8 12)))))))
  (define out (render-chunk img (lookup-placement img 'a)))
  (define input (bytes-append (subbytes out 0 4) (subbytes out 8 12)))
  (check-equal? (subbytes out 16 32) (subbytes (sha256-bytes input) 0 16)))

(test-case "a fixup that does not fit in its chunk is an error"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 2 'rva32 'a)))))
  (check-exn exn:fail? (λ () (render-chunk img (lookup-placement img 'a)))))

(test-case "base relocations come from va32 fixups only"
  (define img (image-of (chunk 'a 4 (make-bytes 24 0)
                               (list (fixup 0 'va32 'b) (digest 8 (list (cons 16 24)))))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define rel (base-relocation-chunk img))
  ; one block: page #x2000, size 12, one HIGHLOW entry at offset 0, padded to 4 bytes
  (check-equal? (chunk-bytes rel)
                (bytes-append (le #x2000 4) (le 12 4) (le #x3000 2) (le 0 2))))

(test-case "file-offset fixup holds the file offset of its target"
  ; headers take 0x200 bytes, so .text raw data starts at 0x200; b follows the 4-byte a
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'file-offset 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (check-equal? (render-chunk img (lookup-placement img 'a)) (le #x204 4))
  (define img2 (image-of (chunk 'a 8 (make-bytes 8 0) '())
                         (chunk 'b 4 (make-bytes 4 0) (list (fixup 0 'file-offset 'a)))))
  (check-equal? (render-chunk img2 (lookup-placement img2 'b)) (le #x200 4)))

(test-case "va64 fixup holds the image base plus the RVA of its target, in 8 bytes"
  (define img (image-of (chunk 'a 8 (make-bytes 8 0) (list (fixup 0 'va64 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define out (render-chunk img (lookup-placement img 'a)))
  (check-equal? out (le (+ #x400000 (placed-rva img 'b)) 8)))

(test-case "a va64 fixup that does not fit in its chunk is an error"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'va64 'a)))))
  (check-exn exn:fail? (λ () (render-chunk img (lookup-placement img 'a)))))

(test-case "an unknown fixup kind is an error"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) (list (fixup 0 'bogus 'a)))))
  (check-exn exn:fail? (λ () (render-chunk img (lookup-placement img 'a)))))

(test-case "base relocations carry HIGHLOW for va32 and DIR64 for va64 sites, in RVA order"
  (define img (image-of (chunk 'a 4 (make-bytes 16 0)
                               (list (fixup 8 'va32 'b) (fixup 0 'va64 'b)))
                        (chunk 'b 4 (make-bytes 4 0) '())))
  (define rel (base-relocation-chunk img))
  (define a-rva (placed-rva img 'a))
  (define page (* #x1000 (quotient a-rva #x1000)))
  (define off (remainder a-rva #x1000))
  ; va64 at a+0 is DIR64 (type 10); va32 at a+8 is HIGHLOW (type 3); body padded to 4 bytes
  (check-equal? (chunk-bytes rel)
                (bytes-append (le page 4) (le 12 4)
                              (le (+ #xA000 off) 2) (le (+ #x3000 off 8) 2))))

(test-case "an image with no fixup sites gets one padding block, so the directory is present"
  (define img (image-of (chunk 'a 4 (make-bytes 4 0) '())))
  (define rel (base-relocation-chunk img))
  (check-equal? (chunk-bytes rel)
                (bytes-append (le (placed-section-rva (car (placed-image-sections img))) 4)
                              (le 12 4) (le 0 2) (le 0 2))))

(test-case "the pe32+ layout uses the 240-byte optional header and 8-byte image base"
  (define params64 (image-params 'pe32+ #x8664 #x22 3 #x8540 #x140000000 #x2000 #x200))
  (define img (layout-image params64 (list (section ".text" #x60000020 (list (chunk 'a 4 (make-bytes 4 0) '()))))))
  (check-equal? (placed-image-headers-size img) #x200)
  (check-equal? (placed-rva img 'a) #x2000))

