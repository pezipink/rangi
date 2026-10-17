#lang racket/base
; Shared fixture plumbing: each fixture is a directory under tests/fixtures/ holding a
; program.rktd. Images are assembled into a fresh temp directory, which is removed afterwards.
(require racket/file racket/port racket/runtime-path racket/string file/sha1
         "../../src/ilasm/syntax.rkt" "../../src/image.rkt")
(provide fixture-names unverified-fixtures fixtures-dir
         with-built-image library-of sha256-hex run-image normalize-newlines)

; Fixtures that neither IL verifier can check. il-unverifiable-opcodes is unverifiable on purpose
; (II.1.7.5). il-runtime-only-opcodes uses TypedReference and calli, which ILVerify does not implement
; and PEVerify rejects. The verifier oracles check these fixtures' metadata only (PEVerify /md) and
; skip them for ILVerify. Their runtime output is still checked.
(define unverified-fixtures '("il-unverifiable-opcodes" "il-runtime-only-opcodes"))

(define-runtime-path fixtures-dir "../fixtures")

; RANGI_FIXTURES=name1,name2 restricts every fixture-based test to the named fixtures.
; Unset runs them all. An unknown name is an error, so a typo cannot silently skip everything.
(define (fixture-names)
  (define all
    (sort
     (for/list ([p (directory-list fixtures-dir)]
                #:when (directory-exists? (build-path fixtures-dir p)))
       (path->string p))
     string<?))
  (define filter-var (getenv "RANGI_FIXTURES"))
  (cond
    [(not filter-var) all]
    [else
     (define wanted
       (for/list ([s (regexp-split #rx"," filter-var)]
                  #:unless (equal? (string-trim s) ""))
         (string-trim s)))
     (define unknown (filter (λ (w) (not (member w all))) wanted))
     (unless (null? unknown)
       (error 'fixture-names "RANGI_FIXTURES names unknown fixtures: ~a" unknown))
     (filter (λ (f) (member f wanted)) all)]))

; calls (proc fixture-dir exe-path) with the program assembled into a temp directory. A fixture
; with a library.rktd also gets library.dll built beside the image, so the host finds it at
; runtime. proc runs with the temp directory as cwd, so .assembly extern "library.dll" resolves.
(define (with-built-image name proc)
  (define dir (build-path fixtures-dir name))
  (define work (make-temporary-file "rangi-fixture-~a" 'directory))
  (dynamic-wind
   void
   (λ ()
     (define exe (build-path work "image.exe"))
     (define library (build-path dir "library.rktd"))
     (when (file-exists? library)
       (assemble (parse-il (call-with-input-file library read)) (library-of exe)))
     (parameterize ([current-directory work])
       (define program (call-with-input-file (build-path dir "program.rktd") read))
       (assemble (parse-il program) exe)
       (proc dir exe)))
   (λ () (delete-directory/files work #:must-exist? #f))))

; the library.dll that with-built-image places beside the image exe
(define (library-of exe)
  (define-values (base name must-be-dir?) (split-path exe))
  (build-path base "library.dll"))

(define (sha256-hex path)
  (call-with-input-file path
    (λ (in) (bytes->hex-string (sha256-bytes in)))))

; returns the exit status and the stdout text of a finished run
(define (run-image exe)
  (define-values (proc out in err) (subprocess #f #f #f exe))
  (close-output-port in)
  (define stdout (port->string out))
  (port->string err)
  (close-input-port out)
  (close-input-port err)
  (subprocess-wait proc)
  (values (subprocess-status proc) stdout))

(define (normalize-newlines s)
  (regexp-replace* #rx"\r\n" s "\n"))
