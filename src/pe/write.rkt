#lang racket/base
; Writes a placed image as a PE32 or PE32+ file (PE/COFF, ECMA-335 II.25.2).
(require "../private/binary.rkt"
         "constants.rkt"
         "layout.rkt")
(provide write-pe-image)

; The 16-bit program at dos-header-size. It prints dos-message, which follows it directly.
(define dos-stub-code
  (bytes #x0E #x1F #xBA #x0E #x00 #xB4 #x09 #xCD #x21 #xB8 #x01 #x4C #xCD #x21))
(define dos-message-offset (+ dos-header-size (bytes-length dos-stub-code)))
(define dos-message (string->bytes/utf-8 "This program cannot be run in DOS mode.\r\r\n$"))

; DOS stub with the standard e_lfanew and the "This program cannot be run" message.
(define dos-header
  (let ([b (make-bytes dos-and-signature-size 0)])
    (bytes-copy! b 0 (bytes #x4D #x5A #x90 #x00 #x03 #x00 #x00 #x00 #x04 #x00 #x00 #x00
                            #xFF #xFF #x00 #x00 #xB8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x40))
    (bytes-copy! b e-lfanew-offset (le pe-header-offset e-lfanew-size))
    (bytes-copy! b dos-header-size dos-stub-code)
    (bytes-copy! b dos-message-offset dos-message)
    (bytes-copy! b pe-header-offset pe-signature-bytes)
    b))

; entry: name of the chunk the entry point jumps to
; dirs: alist of data directory index -> name of the chunk it covers
(define (write-pe-image img out-path #:entry entry #:dirs dirs)
  (define params (placed-image-params img))
  (define pe32+? (eq? (image-params-format params) 'pe32+))
  (define secs (placed-image-sections img))
  (define headers-size (placed-image-headers-size img))
  (define (rva-of name) (placed-rva img name))

  (define (section-raw ps)
    (define buf (make-bytes (placed-section-raw-size ps) 0))
    (for ([p (in-list (placed-section-placements ps))])
      (bytes-copy! buf (- (placement-rva p) (placed-section-rva ps))
                   (render-chunk img p)))
    buf)

  (define (section-header ps)
    (bytes-append (pad-to (string->bytes/utf-8 (placed-section-name ps)) section-name-size)
                  (le (placed-section-vsize ps) 4) (le (placed-section-rva ps) 4)
                  (le (placed-section-raw-size ps) 4) (le (placed-section-raw-ptr ps) 4)
                  (le 0 4) (le 0 4) (le 0 2) (le 0 2) (le (placed-section-chars ps) 4)))

  (define (flagged-sum flag)
    (for/sum ([ps (in-list secs)] #:when (not (zero? (bitwise-and (placed-section-chars ps) flag))))
      (placed-section-raw-size ps)))
  (define (first-flagged-rva flag)
    (or (for/first ([ps (in-list secs)] #:when (not (zero? (bitwise-and (placed-section-chars ps) flag))))
          (placed-section-rva ps))
        0))

  (define dir-bytes
    (apply bytes-append
           (for/list ([i (in-range number-of-data-dirs)])
             (define d (assv i dirs))
             (if d
                 (bytes-append (le (rva-of (cdr d)) 4)
                               (le (chunk-size (placement-chunk (lookup-placement img (cdr d)))) 4))
                 (make-bytes data-dir-entry-size 0)))))

  (define coff-header
    (bytes-append (le (image-params-machine params) 2) (le (length secs) 2) (le 0 4) (le 0 4) (le 0 4)
                  (le (if pe32+? pe32plus-opt-header-size pe32-opt-header-size) 2)
                  (le (image-params-characteristics params) 2)))
  ; PE32+ has no BaseOfData and 8-byte ImageBase and stack/heap fields (II.25.2.3.2)
  (define opt-header
    (bytes-append
     (le (if pe32+? pe32plus-magic pe32-magic) 2)
     (bytes linker-major-version linker-minor-version)
     (le (flagged-sum scn-cnt-code) 4) (le (flagged-sum scn-cnt-initialized-data) 4) (le 0 4)
     (le (rva-of entry) 4) (le (first-flagged-rva scn-cnt-code) 4)
     (if pe32+? #"" (le (first-flagged-rva scn-cnt-initialized-data) 4))
     (if pe32+? (le (image-params-image-base params) 8) (le (image-params-image-base params) 4))
     (le (image-params-section-align params) 4)
     (le (image-params-file-align params) 4)
     (le os-major-version 2) (le 0 2) (le 0 2) (le 0 2)
     (le subsystem-major-version 2) (le 0 2) (le 0 4)
     (le (placed-image-size-of-image img) 4) (le headers-size 4) (le 0 4)
     (le (image-params-subsystem params) 2) (le (image-params-dll-characteristics params) 2)
     (if pe32+?
         (bytes-append (le stack-reserve-size 8) (le stack-commit-size 8)
                       (le heap-reserve-size 8) (le heap-commit-size 8))
         (bytes-append (le stack-reserve-size 4) (le stack-commit-size 4)
                       (le heap-reserve-size 4) (le heap-commit-size 4)))
     (le 0 4) (le number-of-data-dirs 4)
     dir-bytes))

  (define pe-header
    (bytes-append dos-header coff-header opt-header
                  (apply bytes-append (map section-header secs))))
  (define file-bytes
    (apply bytes-append (pad-to pe-header headers-size) (map section-raw secs)))
  (call-with-output-file out-path
    (λ (out) (write-bytes file-bytes out))
    #:exists 'truncate/replace))
