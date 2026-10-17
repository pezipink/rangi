#lang racket/base
; Builds and runs the System.Reflection.Metadata dumper (tests/oracles/srm-dump).
(require racket/system racket/runtime-path)
(provide srm-dotnet build-srm! run-srm run-srm-batch)

(define-runtime-path srm-project "../oracles/srm-dump/srm-dump.csproj")

(define srm-dotnet (find-executable-path "dotnet"))

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
    (error 'srm "srm-dump build failed:\n~a~a" out err)))

; dumps an image with the built dumper; returns the exit code, stdout and stderr
(define (run-srm dotnet exe)
  (run-capture dotnet "run" "--no-build" "--project" (path->string srm-project)
               "--" (path->string exe)))

; dumps many images in one process; the output has a "=== FILE <path>" header per image,
; followed by its dump or a "=== ERROR <message>" line
(define (run-srm-batch dotnet exes)
  (apply run-capture dotnet "run" "--no-build" "--project" (path->string srm-project)
         "--" "--batch" (map path->string exes)))
