#lang racket/base
; Metadata table oracle. System.Reflection.Metadata (tests/oracles/srm-dump) and the Racket
; reader must produce the same dump for every fixture. The approved output is metadata.txt.
(require rackunit racket/system racket/runtime-path
         "../lib/fixture.rkt" "../lib/snapshot.rkt" "../lib/metadata-dump.rkt"
         "../../src/cli-reader.rkt")

(define-runtime-path srm-project "srm-dump/srm-dump.csproj")

; returns the exit code and the stdout and stderr text of a command
(define (run-capture exe . args)
  (define out (open-output-string))
  (define err (open-output-string))
  (define code
    (parameterize ([current-output-port out]
                   [current-error-port err])
      (apply system*/exit-code exe args)))
  (values code (get-output-string out) (get-output-string err)))

(define (build-srm! dotnet)
  (define-values (code out err)
    (run-capture dotnet "build" (path->string srm-project) "-nologo" "-v" "q"))
  (unless (zero? code)
    (error 'metadata-dump-test "srm-dump build failed:\n~a~a" out err)))

(define dotnet (find-executable-path "dotnet"))

(cond
  [dotnet
   (build-srm! dotnet)
   (for ([name (fixture-names)])
     (test-case name
       (with-built-image
        name
        (λ (dir exe)
          (define-values (code srm-out srm-err)
            (run-capture dotnet "run" "--no-build" "--project" (path->string srm-project)
                         "--" (path->string exe)))
          (check-equal? code 0 srm-err)
          (define reader-out (metadata-dump (read-file (path->string exe))))
          (check-equal? (normalize-newlines reader-out) (normalize-newlines srm-out)
                        "reader dump differs from System.Reflection.Metadata")
          (check-snapshot (build-path dir "metadata.txt") reader-out)))))]
  [else
   (printf "skipping metadata oracle: dotnet not found\n")])
