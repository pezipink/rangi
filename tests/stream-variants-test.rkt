#lang racket/base
; Item 1 of the roadmap: the reader must accept an uncompressed "#-" metadata stream with
; HeapSizes 0x40 (II.24.2.6), and must skip unknown streams such as "#!". Variants are built
; by patching the nano fixture, so the same program is the reference for every check.
(require rackunit racket/file racket/path
         "lib/fixture.rkt" "lib/patch-image.rkt" "lib/metadata-dump.rkt" "lib/srm.rkt"
         "../src/cli-reader.rkt")

; RVAs move by 4 bytes when the extra field is inserted; everything else must match
(define (strip-rva s) (regexp-replace* #rx"Rva=[0-9]+" s "Rva=_"))

(define (dump-of path) (metadata-dump (read-file (path->string path))))

(define (write-variant exe name bs)
  (define-values (base _n _d) (split-path exe))
  (define p (build-path base name))
  (call-with-output-file p (λ (o) (write-bytes bs o)) #:exists 'truncate)
  p)

; renames the single "#US" stream header to "#!" (same length, so nothing else moves)
(define (rename-us->bang bs)
  (define needle #"#US\0")
  (define hits
    (for/list ([i (in-range 0 (- (bytes-length bs) (bytes-length needle) -1))]
               #:when (equal? (subbytes bs i (+ i (bytes-length needle))) needle))
      i))
  (unless (= 1 (length hits))
    (error 'rename-us->bang "expected one #US stream name, found ~a" (length hits)))
  (define out (bytes-copy bs))
  (bytes-copy! out (car hits) #"#!\0\0")
  out)

(with-built-image
 "nano"
 (λ (dir exe)
   (define expected-stdout (file->string (build-path dir "expected-stdout.txt")))
   (define uncompressed
     (write-variant exe "uncompressed.exe" (tilde->uncompressed (path->string exe))))
   (define bang
     (write-variant exe "bang.exe" (rename-us->bang (file->bytes uncompressed))))

   (test-case "patched #- image runs"
     (define-values (status stdout) (run-image uncompressed))
     (check-equal? status 0 "exit status")
     (check-equal? (normalize-newlines stdout) (normalize-newlines expected-stdout)))

   (test-case "#- image dump matches the #~ dump apart from RVAs"
     (check-equal? (strip-rva (dump-of uncompressed)) (strip-rva (dump-of exe))))

   (test-case "unknown #! stream is skipped"
     (check-equal? (dump-of bang) (dump-of uncompressed)))

   (when srm-dotnet
     (build-srm! srm-dotnet)
     (for ([variant (list uncompressed bang)])
       (test-case (format "System.Reflection.Metadata agrees on ~a" (let-values ([(_b n _d) (split-path variant)]) n))
         (define-values (code srm-out srm-err) (run-srm srm-dotnet variant))
         (check-equal? code 0 srm-err)
         (check-equal? (normalize-newlines (dump-of variant)) (normalize-newlines srm-out)))))))
