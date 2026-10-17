#lang racket/base
; Base relocation table (PE/COFF .reloc section) for the 'va32 and 'va64 fixups of every chunk.
(require racket/list
         "../private/binary.rkt"
         "constants.rkt"
         "layout.rkt")
(provide base-relocation-chunk)

; base relocation types (PE/COFF base relocation table)
(define reloc-highlow 3)
(define reloc-dir64 10)
(define reloc-absolute 0)
(define page-size #x1000)
; each entry is a 16-bit word: type in the top 4 bits, page offset in the low 12
(define reloc-entry-size 2)
(define reloc-type-shift 12)
(define reloc-block-header-size 8)
; one ABSOLUTE entry padded to dword alignment
(define reloc-padding-block-size 12)

(define (reloc-type kind)
  (case kind
    [(va32) reloc-highlow]
    [(va64) reloc-dir64]
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
        (le (bitwise-ior (arithmetic-shift (cdr s) reloc-type-shift)
                         (remainder (car s) page-size))
            reloc-entry-size)))
    (define body (pad-to (apply bytes-append entries) dword-align))
    (bytes-append (le page 4) (le (+ reloc-block-header-size (bytes-length body)) 4) body))
  (define (padding-block)
    (define page (placed-section-rva (car (placed-image-sections placed))))
    (bytes-append (le page 4) (le reloc-padding-block-size 4)
                  (le reloc-absolute reloc-entry-size) (le 0 reloc-entry-size)))
  (chunk 'reloc dword-align
         (if (null? sites)
             (padding-block)
             (apply bytes-append (map block (group-by (λ (s) (quotient (car s) page-size)) sites))))
         '()))

