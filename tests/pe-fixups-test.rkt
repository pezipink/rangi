#lang racket/base
; Unit tests for the PE fixup model: rva32, va32 and digest fields, and base relocation sites
(require rackunit
         "../src/private/binary.rkt"
         "../src/pe/layout.rkt"
         "../src/pe/relocs.rkt")

(define params (image-params #x400000 #x2000 #x200))

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
