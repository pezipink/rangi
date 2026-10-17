#lang racket/base
; Section and chunk layout for PE images (ECMA-335 II.25.2 and II.25.3).
; This module knows nothing about CLI metadata. A chunk is a named blob of
; bytes that may refer to other chunks through a resolver (name -> RVA).
(require "../private/binary.rkt")
(provide (struct-out image-params)
         (struct-out chunk)
         (struct-out section)
         (struct-out placement)
         (struct-out placed-section)
         (struct-out placed-image)
         bytes-chunk linked-chunk chunk-bytes
         layout-image layout-report lookup-placement placed-rva)

(struct image-params (image-base section-align file-align))

; data is either bytes, or a procedure (name -> RVA) -> bytes for chunks that
; hold addresses. size must equal the length of the rendered bytes.
(struct chunk (name align size data relocs))

; name: string; chars: section characteristics
(struct section (name chars chunks))

; rva: absolute RVA of the chunk
(struct placement (chunk rva))

(struct placed-section (name chars rva vsize raw-ptr raw-size placements))

; symbols: hasheq from chunk name to placement
(struct placed-image (params headers-size sections size-of-image symbols))

(define (bytes-chunk name align bs [relocs '()])
  (chunk name align (bytes-length bs) bs relocs))

(define (linked-chunk name align size proc [relocs '()])
  (chunk name align size proc relocs))

; DOS header with PE signature (0x84) + COFF header (20) + PE32 optional header (224)
(define fixed-header-size #x178)
(define section-header-size 40)

(define (chunk-bytes c rva-of)
  (define d (chunk-data c))
  (define bs (if (bytes? d) d (d rva-of)))
  (unless (= (bytes-length bs) (chunk-size c))
    (error 'rangi "chunk ~a is ~a bytes, expected ~a"
           (chunk-name c) (bytes-length bs) (chunk-size c)))
  bs)

; places chunks in order inside a section starting at base; returns the
; placements and the section's virtual size
(define (place-chunks base chunks)
  (define-values (rev end)
    (for/fold ([acc '()] [pos 0]) ([c (in-list chunks)])
      (define off (align pos (chunk-align c)))
      (values (cons (placement c (+ base off)) acc) (+ off (chunk-size c)))))
  (values (reverse rev) end))

; Sections are laid out in order. The first section starts at the first
; section-align boundary after the headers, and each section starts at the next
; boundary after the previous one. Raw data is file-align padded.
(define (layout-image params secs)
  (define sa (image-params-section-align params))
  (define fa (image-params-file-align params))
  (define headers-size
    (align (+ fixed-header-size (* section-header-size (length secs))) fa))
  (define-values (placed rva-end _raw-end)
    (for/fold ([acc '()] [rva (align headers-size sa)] [raw headers-size])
              ([s (in-list secs)])
      (define-values (ps vsize) (place-chunks rva (section-chunks s)))
      (define raw-size (align vsize fa))
      (values (cons (placed-section (section-name s) (section-chars s) rva vsize raw raw-size ps)
                    acc)
              (align (+ rva vsize) sa)
              (+ raw raw-size))))
  (define sections (reverse placed))
  (define symbols (make-hasheq))
  (for* ([ps (in-list sections)] [p (in-list (placed-section-placements ps))])
    (define n (chunk-name (placement-chunk p)))
    (when (hash-ref symbols n #f)
      (error 'rangi "duplicate chunk name ~a" n))
    (hash-set! symbols n p))
  (placed-image params headers-size sections rva-end symbols))

; one line per section and per chunk, with RVAs and file offsets, for snapshot tests (V5)
(define (layout-report img)
  (define out (open-output-string))
  (define (hex n) (number->string n 16))
  (define (line fmt . args)
    (write-string (apply format fmt args) out)
    (newline out))
  (line "headers size 0x~a" (hex (placed-image-headers-size img)))
  (line "size-of-image 0x~a" (hex (placed-image-size-of-image img)))
  (for ([s (in-list (placed-image-sections img))])
    (line "section ~a rva 0x~a vsize 0x~a raw 0x~a raw-size 0x~a"
          (placed-section-name s) (hex (placed-section-rva s)) (hex (placed-section-vsize s))
          (hex (placed-section-raw-ptr s)) (hex (placed-section-raw-size s)))
    (for ([p (in-list (placed-section-placements s))])
      (define c (placement-chunk p))
      (define file-off
        (+ (placed-section-raw-ptr s) (- (placement-rva p) (placed-section-rva s))))
      (line "  ~a rva 0x~a file 0x~a size 0x~a align 0x~a"
            (chunk-name c) (hex (placement-rva p)) (hex file-off)
            (hex (chunk-size c)) (hex (chunk-align c)))))
  (get-output-string out))

(define (lookup-placement img name)
  (hash-ref (placed-image-symbols img) name
            (λ () (error 'rangi "no chunk named ~a" name))))

(define (placed-rva img name)
  (placement-rva (lookup-placement img name)))
