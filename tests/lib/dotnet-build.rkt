#lang racket/base
; Builds an oracle project with dotnet. Test files run in parallel processes (raco test -j), and
; two dotnet builds of one project in the same obj/ folder can fail, so the build holds a
; machine-wide file lock. After the first build the rest are incremental no-ops.
(require racket/system racket/file)
(provide dotnet-build!)

(define lock-file (build-path (find-system-path 'temp-dir) "rangi-dotnet-build.lock"))

; builds project (a path or string) and raises an error with the output when the build fails
(define (dotnet-build! dotnet project)
  (define project-arg (if (path? project) (path->string project) project))
  (call-with-file-lock/timeout
   lock-file 'exclusive
   (λ ()
     (define out (open-output-string))
     (define code
       (parameterize ([current-output-port out]
                      [current-error-port out])
         (system*/exit-code dotnet "build" project-arg "-nologo" "-v" "q")))
     (unless (zero? code)
       (error 'dotnet-build "build of ~a failed:\n~a" project (get-output-string out))))
   (λ () (error 'dotnet-build "could not take the build lock ~a" lock-file))
   #:max-delay 900))
