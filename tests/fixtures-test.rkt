#lang racket/base
; L4 image hash and L7 execution for every fixture under tests/fixtures/
(require rackunit "lib/fixture.rkt" "lib/snapshot.rkt")

(for ([name (fixture-names)])
  (test-case name
    (with-built-image
     name
     (λ (dir exe)
       (check-snapshot (build-path dir "image.sha256") (string-append (sha256-hex exe) "\n"))
       (define-values (status stdout) (run-image exe))
       (check-equal? status 0 "exit status")
       (check-snapshot (build-path dir "expected-stdout.txt") (normalize-newlines stdout))))))
