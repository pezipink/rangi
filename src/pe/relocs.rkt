#lang racket/base
; Base relocation table (PE/COFF .reloc section) for the 'va32 fixups of every chunk.
(require racket/list
         "../private/binary.rkt"
         "layout.rkt")
(provide base-relocation-chunk)

(define highlow 3)
(define page-size #x1000)

; One block per 4K page: page RVA, block size, then 16-bit entries (type in the
; top 4 bits, page offset in the low 12), padded to a multiple of 4 bytes.
(define (base-relocation-chunk placed)
  (define sites
    (sort (for*/list ([ps (in-list (placed-image-sections placed))]
                      [p (in-list (placed-section-placements ps))]
                      [f (in-list (chunk-fixups (placement-chunk p)))]
                      #:when (and (fixup? f) (eq? (fixup-kind f) 'va32)))
            (+ (placement-rva p) (fixup-offset f)))
          <))
  (define (block group)
    (define page (* page-size (quotient (car group) page-size)))
    (define entries
      (for/list ([s (in-list group)])
        (le (bitwise-ior (arithmetic-shift highlow 12) (remainder s page-size)) 2)))
    (define body (pad-to (apply bytes-append entries) 4))
    (bytes-append (le page 4) (le (+ 8 (bytes-length body)) 4) body))
  (chunk 'reloc 4
         (apply bytes-append (map block (group-by (λ (s) (quotient s page-size)) sites)))
         '()))
