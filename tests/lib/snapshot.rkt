#lang racket/base
; Compares generated text with an approved snapshot file. Set RANGI_UPDATE_SNAPSHOTS=1
; to rewrite the snapshot instead of comparing against it.
(require rackunit racket/file)
(provide check-snapshot)

(define update-snapshots? (and (getenv "RANGI_UPDATE_SNAPSHOTS") #t))

(define (check-snapshot path actual)
  (cond
    [update-snapshots?
     (make-parent-directory* path)
     (display-to-file actual path #:exists 'replace)]
    [(not (file-exists? path))
     (fail (format "missing snapshot ~a (run with RANGI_UPDATE_SNAPSHOTS=1 to create it)" path))]
    [else
     ; snapshots compare with LF line endings, whatever the checkout produced
     (check-equal? (regexp-replace* #rx"\r\n" actual "\n")
                   (regexp-replace* #rx"\r\n" (file->string path) "\n")
                   (format "snapshot ~a" path))]))
