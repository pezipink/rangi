#lang racket/base
; Round trip: write a small PE32 image, read its headers back with pe/read.rkt, and check that
; RVA-to-file-offset agrees with the placements the layout engine recorded
(require rackunit
         racket/file
         "../src/pe/layout.rkt"
         "../src/pe/read.rkt"
         "../src/pe/write.rkt")

(define params (image-params 'pe32 #x14C #x102 3 #x8540 #x400000 #x2000 #x200))

(define img
  (layout-image params
                (list (section ".text" #x60000020
                               (list (chunk 'entry 4 (make-bytes 4 0) '())
                                     (chunk 'data 8 (make-bytes 8 0) '()))))))

(define path (make-temporary-file "rangi-pe-read-~a.exe"))

(test-case "the reader maps every placed RVA to the file offset the layout recorded"
  (write-pe-image img path #:entry 'entry #:dirs '())
  (define hdrs (call-with-input-file path read-pe-headers))
  (check-equal? (length (hash-ref hdrs 'sec-headers)) 1)
  (check-equal? (integer-bytes->integer (hash-ref (hash-ref hdrs 'pe-opt) 'image-base) #f #f)
                #x400000)
  (for* ([ps (in-list (placed-image-sections img))]
         [p (in-list (placed-section-placements ps))])
    (check-equal? (rva->file-offset hdrs (placement-rva p)) (placement-file-offset p)
                  (format "chunk ~a" (chunk-name (placement-chunk p))))))

(test-case "the reader accepts a PE32+ image and reads its 8-byte image base"
  (define params64 (image-params 'pe32+ #x8664 #x22 3 #x8540 #x140000000 #x2000 #x200))
  (define img64 (layout-image params64 (list (section ".text" #x60000020
                                                      (list (chunk 'entry 4 (make-bytes 4 0) '()))))))
  (define path64 (make-temporary-file "rangi-pe64-read-~a.exe"))
  (write-pe-image img64 path64 #:entry 'entry #:dirs '())
  (define hdrs (call-with-input-file path64 read-pe-headers))
  (check-equal? (integer-bytes->integer (hash-ref (hash-ref hdrs 'pe-opt) 'image-base) #f #f)
                #x140000000)
  (check-equal? (rva->file-offset hdrs #x2000) #x200)
  (delete-file path64))


(test-case "an RVA outside every section is an error"
  (define hdrs (call-with-input-file path read-pe-headers))
  (check-exn exn:fail? (λ () (rva->file-offset hdrs #x100))))

(delete-file path)
