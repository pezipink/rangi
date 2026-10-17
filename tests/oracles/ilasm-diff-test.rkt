#lang racket/base
; Differential ilasm oracle. Fixtures with a textual program.il are assembled by the real ilasm.exe
; and by Rangi. Both images must print the approved expected-stdout.txt, and their
; System.Reflection.Metadata dumps must agree after normalisation (see lib/srm-normalize.rkt).
(require rackunit racket/file
         "../lib/fixture.rkt" "../lib/srm.rkt" "../lib/srm-normalize.rkt" "tools.rkt")

(define ilasm (find-ilasm))

(define (ilasm-fixture-names)
  (filter (λ (name) (file-exists? (build-path fixtures-dir name "program.il")))
          (fixture-names)))

(define (assemble-with-ilasm ilasm-exe il exe)
  (define-values (code out)
    (run-tool ilasm-exe (list "/nologo" (string-append "/output:" (path->string exe))
                              (path->string il))
              exe))
  (check-equal? code 0 (string-append "ilasm failed: " out))
  (check-true (file-exists? exe) "ilasm did not write the image"))

(cond
  [(not ilasm) (oracle-missing "ilasm.exe")]
  [(not srm-dotnet) (oracle-missing "dotnet")]
  [else
   (build-srm! srm-dotnet)
   (for ([name (ilasm-fixture-names)])
     (test-case name
       (define dir (build-path fixtures-dir name))
       (define expected (normalize-newlines (file->string (build-path dir "expected-stdout.txt"))))
       (define work (make-temporary-file "rangi-ilasm-~a" 'directory))
       (dynamic-wind
        void
        (λ ()
          (define oracle-exe (build-path work "oracle.exe"))
          (assemble-with-ilasm ilasm (build-path dir "program.il") oracle-exe)
          (with-built-image
           name
           (λ (_ rangi-exe)
             (define-values (oracle-status oracle-out) (run-image oracle-exe))
             (check-equal? oracle-status 0 "ilasm image exit status")
             (check-equal? (normalize-newlines oracle-out) expected "ilasm image stdout")
             (define-values (rangi-status rangi-out) (run-image rangi-exe))
             (check-equal? rangi-status 0 "Rangi image exit status")
             (check-equal? (normalize-newlines rangi-out) expected "Rangi image stdout")
             (define-values (oracle-code oracle-dump oracle-err) (run-srm srm-dotnet oracle-exe))
             (check-equal? oracle-code 0 oracle-err)
             (define-values (rangi-code rangi-dump rangi-err) (run-srm srm-dotnet rangi-exe))
             (check-equal? rangi-code 0 rangi-err)
             (check-equal? (normalize-srm-dump (normalize-newlines rangi-dump))
                           (normalize-srm-dump (normalize-newlines oracle-dump))
                           "normalised metadata differs from ilasm"))))
        (λ () (delete-directory/files work #:must-exist? #f)))))])
