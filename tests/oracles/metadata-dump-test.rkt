#lang racket/base
; Metadata table oracle. System.Reflection.Metadata (tests/oracles/srm-dump) and the Racket
; reader must produce the same dump for every fixture. The approved output is metadata.txt.
(require rackunit
         "../lib/fixture.rkt" "../lib/snapshot.rkt" "../lib/metadata-dump.rkt" "../lib/srm.rkt"
         "../../src/cli-reader.rkt" "tools.rkt")

(cond
  [srm-dotnet
   (build-srm! srm-dotnet)
   (for ([name (fixture-names)])
     (test-case name
       (with-built-image
        name
        (λ (dir exe)
          (define-values (code srm-out srm-err) (run-srm srm-dotnet exe))
          (check-equal? code 0 srm-err)
          (define reader-out (metadata-dump (read-file (path->string exe))))
          (check-equal? (normalize-newlines reader-out) (normalize-newlines srm-out)
                        "reader dump differs from System.Reflection.Metadata")
          (check-snapshot (build-path dir "metadata.txt") reader-out)))))]
  [else
   (oracle-missing "dotnet")])
