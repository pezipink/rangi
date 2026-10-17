#lang racket/base
; Section and chunk layout for PE images (ECMA-335 II.25.2 and II.25.3).
; This module knows nothing about CLI metadata. The structs are in model.rkt.
(require "../private/binary.rkt"
         "model.rkt")
(provide (all-from-out "model.rkt")
         chunk-size fixup-size render-chunk
         layout-image layout-report lookup-placement placed-rva)

(define (chunk-size c) (bytes-length (chunk-bytes c)))

; width in bytes of the field a fixup kind fills in
(define (fixup-size kind)
  (case kind
    [(rva32 va32 file-offset) 4]
    [(va64) 8]
    [else (error 'rangi "unknown fixup kind ~a" kind)]))

; copies the chunk bytes and fills each fixup and digest once layout is known
(define (render-chunk img p)
  (define c (placement-chunk p))
  (define bs (bytes-copy (chunk-bytes c)))
  (define base (image-params-image-base (placed-image-params img)))
  (define (check-field off size)
    (unless (<= 0 off (- (bytes-length bs) size))
      (error 'rangi "fixup at 0x~a is outside chunk ~a (~a bytes)"
             (number->string off 16) (chunk-name c) (bytes-length bs))))
  (for ([f (in-list (chunk-fixups c))] #:when (fixup? f))
    (define off (fixup-offset f))
    (define size (fixup-size (fixup-kind f)))
    (check-field off size)
    (define target (fixup-target f))
    (define value
      (case (fixup-kind f)
        [(rva32) (placed-rva img target)]
        [(va32 va64) (+ base (placed-rva img target))]
        [(file-offset) (placement-file-offset (lookup-placement img target))]))
    (bytes-copy! bs off (le value size)))
  (for ([d (in-list (chunk-fixups c))] #:when (digest? d))
    (define off (digest-offset d))
    (unless (<= 0 off (- (bytes-length bs) 16))
      (error 'rangi "digest at 0x~a is outside chunk ~a" (number->string off 16) (chunk-name c)))
    (define input
      (apply bytes-append (for/list ([s (in-list (digest-spans d))])
                            (subbytes bs (car s) (cdr s)))))
    (bytes-copy! bs off (subbytes (sha256-bytes input) 0 16)))
  bs)

; DOS header with PE signature (0x84) + COFF header (20) + optional header
; (224 bytes for PE32, 240 for PE32+)
(define (fixed-header-size params)
  (+ #x84 20 (if (eq? (image-params-format params) 'pe32+) 240 224)))
(define section-header-size 40)

; places chunks in order inside a section starting at rva and raw at file offset raw;
; returns the placements and the section's virtual size
(define (place-chunks rva raw chunks)
  (define-values (rev end)
    (for/fold ([acc '()] [pos 0]) ([c (in-list chunks)])
      (define off (align-up pos (chunk-align c)))
      (values (cons (placement c (+ rva off) (+ raw off)) acc) (+ off (chunk-size c)))))
  (values (reverse rev) end))

; Sections are laid out in order. The first section starts at the first
; section-align boundary after the headers, and each section starts at the next
; boundary after the previous one. Raw data is file-align padded.
(define (layout-image params secs)
  (define sa (image-params-section-align params))
  (define fa (image-params-file-align params))
  (define headers-size
    (align-up (+ (fixed-header-size params) (* section-header-size (length secs))) fa))
  (define-values (placed rva-end _raw-end)
    (for/fold ([acc '()] [rva (align-up headers-size sa)] [raw headers-size])
              ([s (in-list secs)])
      (define-values (ps vsize) (place-chunks rva raw (section-chunks s)))
      (define raw-size (align-up vsize fa))
      (values (cons (placed-section (section-name s) (section-chars s) rva vsize raw raw-size ps)
                    acc)
              (align-up (+ rva vsize) sa)
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
      (define file-off (placement-file-offset p))
      (line "  ~a rva 0x~a file 0x~a size 0x~a align 0x~a"
            (chunk-name c) (hex (placement-rva p)) (hex file-off)
            (hex (chunk-size c)) (hex (chunk-align c)))))
  (get-output-string out))

(define (lookup-placement img name)
  (hash-ref (placed-image-symbols img) name
            (λ () (error 'rangi "no chunk named ~a" name))))

(define (placed-rva img name)
  (placement-rva (lookup-placement img name)))
