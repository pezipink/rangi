#lang racket/base
; Locates the external .NET Framework tools used by the oracle tests. Set RANGI_PEVERIFY or
; RANGI_ILDASM to override the default SDK paths.
(require racket/system racket/string racket/port)
(provide find-tool run-tool oracle-missing)

(define sdk-tools "C:\\Program Files (x86)\\Microsoft SDKs\\Windows\\v10.0A\\bin\\NETFX 4.6.1 Tools\\")

; returns the path of the tool, or #f when it is not installed
(define (find-tool env-var exe-name)
  (for/first ([candidate (list (getenv env-var) (build-path sdk-tools exe-name))]
              #:when (and candidate (file-exists? candidate)))
    candidate))

; called when an oracle's tool is missing. By default the oracle is skipped with a message. When
; RANGI_REQUIRE_ORACLES is set to a non-empty value other than 0, the missing tool is an error,
; so a machine without the tools cannot pass the verification suite silently.
(define (oracle-missing what)
  (define required (getenv "RANGI_REQUIRE_ORACLES"))
  (if (and required (not (member required '("" "0"))))
      (error 'oracle "~a not found and RANGI_REQUIRE_ORACLES is set" what)
      (printf "skipping oracle: ~a not found (set RANGI_REQUIRE_ORACLES=1 to fail instead)\n" what)))

; runs the tool with args and returns its exit code and combined output. the image path is
; replaced with <image> so that snapshots do not depend on the temp directory name
(define (run-tool tool args image)
  (define out (open-output-string))
  (define code
    (parameterize ([current-output-port out]
                   [current-error-port out])
      (apply system*/exit-code tool args)))
  (values code (string-replace (get-output-string out) (path->string image) "<image>")))
