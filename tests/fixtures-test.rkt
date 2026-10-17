#lang racket/base
; L4 image hash and L7 execution for every fixture under tests/fixtures/
(require rackunit racket/file "lib/fixture.rkt" "lib/snapshot.rkt"
         "../src/ilasm/syntax.rkt" "../src/image.rkt")

; fixtures that exist to push .text past a layout threshold (roadmap P3); each must stay above it
(define text-floors (hash "text-over-400" #x400 "text-over-2000" #x2000))

; VirtualSize of the .text section, read from the PE section table
(define (text-vsize bs)
  (define (le p n) (integer-bytes->integer bs #f #f p (+ p n)))
  (define pe (le #x3C 4))
  (define coff (+ pe 4))
  (define sections (+ pe 24 (le (+ coff 16) 2)))
  (for/or ([i (in-range (le (+ coff 2) 2))])
    (define s (+ sections (* 40 i)))
    (and (equal? (subbytes bs s (+ s 5)) #".text") (le (+ s 8) 4))))

(for ([name (fixture-names)])
  (test-case name
    (with-built-image
     name
     (λ (dir exe)
       (check-snapshot (build-path dir "image.sha256") (string-append (sha256-hex exe) "\n"))
       (define program (call-with-input-file (build-path dir "program.rktd") read))
       (check-snapshot (build-path dir "layout.txt") (image-layout-report (parse-il program)))
       (define library (library-of exe))
       (when (file-exists? library)
         (check-snapshot (build-path dir "library.sha256") (string-append (sha256-hex library) "\n"))
         (define library-program (call-with-input-file (build-path dir "library.rktd") read))
         (check-snapshot (build-path dir "library-layout.txt")
                         (image-layout-report (parse-il library-program) "library.dll")))
       (define-values (status stdout) (run-image exe))
       (check-equal? status 0 "exit status")
       (check-snapshot (build-path dir "expected-stdout.txt") (normalize-newlines stdout))
       (define threshold (hash-ref text-floors name #f))
       (when threshold
         (check-true (> (text-vsize (file->bytes exe)) threshold)
                     (format ".text VirtualSize must exceed 0x~a" (number->string threshold 16))))))))
