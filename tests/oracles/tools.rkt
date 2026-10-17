#lang racket/base
; Locates the external .NET Framework tools used by the oracle tests. Set RANGI_PEVERIFY or
; RANGI_ILDASM to override the default SDK paths.
(require racket/system racket/string racket/port)
(provide find-tool run-tool)

(define sdk-tools "C:\\Program Files (x86)\\Microsoft SDKs\\Windows\\v10.0A\\bin\\NETFX 4.6.1 Tools\\")

; returns the path of the tool, or #f when it is not installed
(define (find-tool env-var exe-name)
  (for/first ([candidate (list (getenv env-var) (build-path sdk-tools exe-name))]
              #:when (and candidate (file-exists? candidate)))
    candidate))

; runs the tool with args and returns its exit code and combined output. the image path is
; replaced with <image> so that snapshots do not depend on the temp directory name
(define (run-tool tool args image)
  (define out (open-output-string))
  (define code
    (parameterize ([current-output-port out]
                   [current-error-port out])
      (apply system*/exit-code tool args)))
  (values code (string-replace (get-output-string out) (path->string image) "<image>")))
