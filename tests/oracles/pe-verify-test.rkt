#lang racket/base
; PEVerify (.NET Framework SDK) oracle. The approved output per fixture is pe-verify.txt, so a
; change in the verifier's findings for an image fails until the new output is reviewed.
(require rackunit "../lib/fixture.rkt" "../lib/snapshot.rkt" "tools.rkt")

(define pe-verify (find-tool "RANGI_PEVERIFY" "PEVerify.exe"))

(if pe-verify
    (for ([name (fixture-names)])
      (test-case name
        (with-built-image
         name
         (λ (dir exe)
           (define-values (code out)
             (run-tool pe-verify (list "/md" "/il" "/nologo" (path->string exe)) exe))
           (check-snapshot (build-path dir "pe-verify.txt") (format "exit ~a\n~a" code out))))))
    (printf "skipping PEVerify oracle: PEVerify.exe not found\n"))
