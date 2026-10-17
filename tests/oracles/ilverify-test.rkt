#lang racket/base
; ILVerify oracle (Microsoft.ILVerification, tests/oracles/ilverify). Each fixture image is
; verified against the .NET Framework 4.7.1 reference assemblies. Any verification error fails
; the fixture, and the verifier's messages are part of the failure output.
(require rackunit racket/runtime-path "../lib/fixture.rkt" "tools.rkt")

(define-runtime-path ilverify-project "ilverify/ilverify.csproj")

(define dotnet (find-dotnet))
(define reference-dir (find-directory "RANGI_REFERENCE_ASSEMBLIES" net471-reference-dir))

(cond
  [(and dotnet reference-dir)
   (define project (path->string ilverify-project))
   (define-values (build-code build-out)
     (run-tool dotnet (list "build" project "-nologo" "-v" "q") ilverify-project))
   (unless (zero? build-code)
     (error 'ilverify "ilverify build failed:\n~a" build-out))
   (for ([name (fixture-names)])
     (test-case name
       (with-built-image
        name
        (λ (dir exe)
          (define-values (code out)
            (run-tool dotnet
                      (list "run" "--no-build" "--project" project
                            "--" (path->string exe) reference-dir)
                      exe))
          (check-equal? code 0 (string-append "ILVerify reported errors:\n" out))))))]
  [(not dotnet) (oracle-missing "dotnet")]
  [else (oracle-missing ".NET Framework 4.7.1 reference assemblies")])
