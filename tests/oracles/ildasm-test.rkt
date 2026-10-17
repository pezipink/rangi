#lang racket/base
; ildasm oracle. The approved disassembly per fixture is ildasm.il, with the per-build MVID
; and image base comments removed so that only real changes show up in the diff.
(require rackunit racket/string "../lib/fixture.rkt" "../lib/snapshot.rkt" "tools.rkt")

(define ildasm (find-tool "RANGI_ILDASM" "ildasm.exe"))

(define (scrub-volatile-lines text)
  (string-join
   (for/list ([line (string-split text "\n" #:trim? #f)]
              #:unless (regexp-match? #rx"^// (MVID|Image base):" line))
     line)
   "\n"))

(if ildasm
    (for ([name (fixture-names)])
      (test-case name
        (with-built-image
         name
         (λ (dir exe)
           (define-values (code out) (run-tool ildasm (list "/all" "/text" "/nobar" (path->string exe)) exe))
           (check-equal? code 0 "ildasm exit status")
           (check-snapshot (build-path dir "ildasm.il") (scrub-volatile-lines out))))))
    (oracle-missing "ildasm.exe"))
