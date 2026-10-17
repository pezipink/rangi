#lang racket/base
; Base relocation table (PE/COFF .reloc section) for the 'va32 and 'va64 fixups of every chunk.
(require racket/list
         "../private/binary.rkt"
         "layout.rkt")
(provide base-relocation-chunk)

(define highlow 3)
(define dir64 10)
(define page-size #x1000)

(define (reloc-type kind)
  (case kind
    [(va32) highlow]
    [(va64) dir64]
    [else #f]))

; One block per 4K page: page RVA, block size, then 16-bit entries (type in the
; top 4 bits, page offset in the low 12), padded to a multiple of 4 bytes.
; With no sites the table holds one ABSOLUTE padding block (type 0, a no-op) so the
; directory is still present for images with DYNAMIC_BASE set.
(define (base-relocation-chunk placed)
  (define sites
    (sort (for*/list ([ps (in-list (placed-image-sections placed))]
                      [p (in-list (placed-section-placements ps))]
                      [f (in-list (chunk-fixups (placement-chunk p)))]
                      #:when (and (fixup? f) (reloc-type (fixup-kind f))))
            (cons (+ (placement-rva p) (fixup-offset f)) (reloc-type (fixup-kind f))))
          < #:key car))
  (define (block group)
    (define page (* page-size (quotient (car (car group)) page-size)))
    (define entries
      (for/list ([s (in-list group)])
        (le (bitwise-ior (arithmetic-shift (cdr s) 12) (remainder (car s) page-size)) 2)))
    (define body (pad-to (apply bytes-append entries) 4))
    (bytes-append (le page 4) (le (+ 8 (bytes-length body)) 4) body))
  (define (padding-block)
    (define page (placed-section-rva (car (placed-image-sections placed))))
    (bytes-append (le page 4) (le 12 4) (le 0 2) (le 0 2)))
  (chunk 'reloc 4
         (if (null? sites)
             (padding-block)
             (apply bytes-append (map block (group-by (λ (s) (quotient (car s) page-size)) sites))))
         '()))

