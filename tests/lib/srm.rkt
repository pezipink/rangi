#lang racket/base
; Builds and runs the System.Reflection.Metadata dumpers: srm-dump (tests/oracles/srm-dump) and
; pdb-dump (tests/oracles/pdb-dump), which reads portable PDBs and debug directories.
(require racket/system racket/runtime-path "dotnet-build.rkt")
(provide srm-dotnet build-srm! run-srm run-srm-batch build-pdb-dump! run-pdb-dump)

(define-runtime-path srm-project "../oracles/srm-dump/srm-dump.csproj")
(define-runtime-path pdb-dump-project "../oracles/pdb-dump/pdb-dump.csproj")

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
  (dotnet-build! dotnet srm-project))

(define (build-pdb-dump! dotnet)
  (dotnet-build! dotnet pdb-dump-project))

; dumps a portable PDB, or the debug directory of an image, with the built pdb-dump
(define (run-pdb-dump dotnet path)
  (run-capture dotnet "run" "--no-build" "--project" (path->string pdb-dump-project)
               "--" (path->string path)))

; dumps an image with the built dumper; returns the exit code, stdout and stderr
(define (run-srm dotnet exe)
  (run-capture dotnet "run" "--no-build" "--project" (path->string srm-project)
               "--" (path->string exe)))

; dumps many images in one process; the output has a "=== FILE <path>" header per image,
; followed by its dump or a "=== ERROR <message>" line
(define (run-srm-batch dotnet exes)
  (apply run-capture dotnet "run" "--no-build" "--project" (path->string srm-project)
         "--" "--batch" (map path->string exes)))
