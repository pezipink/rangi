#lang racket/base
; Reader corpus. The L3 dump of every table that Rangi's reader decodes (tests/lib/metadata-dump.rkt)
; must match System.Reflection.Metadata (tests/oracles/srm-dump) row for row on real assemblies:
; the .NET Framework 4.7.1 reference assemblies and the newest .NET 10 System.Private.CoreLib.
(require rackunit racket/path racket/list racket/string
         "../lib/fixture.rkt" "../lib/metadata-dump.rkt" "../lib/srm.rkt"
         "../../src/cli-reader.rkt" "tools.rkt")

(define reference-dir
  "C:\\Program Files (x86)\\Reference Assemblies\\Microsoft\\Framework\\.NETFramework\\v4.7.1")
(define shared-dir "C:\\Program Files\\dotnet\\shared\\Microsoft.NETCore.App")

; native image with no CLI header; read-file cannot parse it, so it is not part of the corpus
(define excluded-reference-dlls '("System.EnterpriseServices.Thunk.dll"))

(define (version-numbers name) (map string->number (string-split name ".")))

(define (version-newer? a b)
  (cond [(null? a) #f]
        [(null? b) #t]
        [(> (car a) (car b)) #t]
        [(< (car a) (car b)) #f]
        [else (version-newer? (cdr a) (cdr b))]))

(define (corelib-path)
  (define runtimes
    (for/list ([d (in-list (directory-list shared-dir #:build? #t))]
               #:when (regexp-match? #rx"^10[.]" (path->string (file-name-from-path d))))
      d))
  (define newest
    (car (sort runtimes
               (λ (x y) (version-newer? (version-numbers (path->string (file-name-from-path x)))
                                        (version-numbers (path->string (file-name-from-path y))))))))
  (build-path newest "System.Private.CoreLib.dll"))

; directory-list sorts its results, so the corpus order is stable across runs
(define (corpus-files)
  (append
   (for/list ([p (in-list (directory-list reference-dir #:build? #t))]
              #:when (regexp-match? #rx"(?i:[.]dll$)" (path->string p))
              #:unless (member (path->string (file-name-from-path p)) excluded-reference-dlls))
     p)
   (list (corelib-path))))

; maps each requested path to (cons 'ok dump) or (cons 'error message)
(define (parse-batch files out)
  (define starts (map car (regexp-match-positions* #rx"(?m:^=== FILE )" out)))
  (define ends (append (cdr starts) (list (string-length out))))
  (for/hash ([s (in-list starts)] [e (in-list ends)])
    (define chunk (substring out s e))
    (define header-end (car (regexp-match-positions #rx"\n" chunk)))
    (define path (substring chunk (string-length "=== FILE ") (car header-end)))
    (define body (substring chunk (cdr header-end)))
    (values path
            (cond [(regexp-match #rx"^=== ERROR ([^\n]*)" body)
                   => (λ (m) (cons 'error (cadr m)))]
                  [else (cons 'ok body)]))))

; #f when the dumps match; otherwise the number of differing lines and the first one,
; labelled with the table header it sits under
(define (diff-summary reader srm)
  (define a (list->vector (string-split (normalize-newlines reader) "\n" #:trim? #f)))
  (define b (list->vector (string-split (normalize-newlines srm) "\n" #:trim? #f)))
  (define n (max (vector-length a) (vector-length b)))
  (define (line v i) (if (< i (vector-length v)) (vector-ref v i) "<end of dump>"))
  (define diffs
    (for/list ([i (in-range n)] #:unless (equal? (line a i) (line b i))) i))
  (define (table-of v i)
    (or (for/first ([j (in-range i -1 -1)]
                    #:when (and (>= j 0)
                                (not (string-prefix? (vector-ref v j) " "))
                                (not (string=? (vector-ref v j) ""))))
          (vector-ref v j))
        "<no table>"))
  (and (pair? diffs)
       (let ([i (car diffs)])
         (format "~a of ~a lines differ; first at line ~a (under '~a'):\n  reader: ~a\n  srm:    ~a"
                 (length diffs) n (add1 i) (table-of a i) (line a i) (line b i)))))

(define (ms-since t0) (round (- (current-inexact-milliseconds) t0)))

(define corpus-start (current-inexact-milliseconds))

; targeted runs set RANGI_SKIP_CORPUS=1 to skip this ~30 s oracle. Full section-end runs leave it unset.
(define skip-corpus? (let ([v (getenv "RANGI_SKIP_CORPUS")]) (and v (not (member v '("" "0"))))))

(cond
  [skip-corpus?
   (printf "skipping reader corpus (RANGI_SKIP_CORPUS is set)\n")]
  [srm-dotnet
   (build-srm! srm-dotnet)
   (define files (corpus-files))
   (define srm-start (current-inexact-milliseconds))
   (define-values (code srm-out srm-err) (run-srm-batch srm-dotnet files))
   (printf "SRM batch over ~a images: ~a ms\n" (length files) (ms-since srm-start))
   (unless (zero? code)
     (error 'reader-corpus "srm-dump batch failed:\n~a~a" srm-out srm-err))
   (define srm-results (parse-batch files srm-out))
   (for ([path (in-list files)])
     (define name (path->string (file-name-from-path path)))
     (test-case name
       (define srm-result (hash-ref srm-results (path->string path)
                                    (λ () (fail (format "srm-dump printed no entry for ~a" name)))))
       (case (car srm-result)
         [(error) (fail (format "srm-dump could not read ~a: ~a" name (cdr srm-result)))]
         [else
          (define reader-start (current-inexact-milliseconds))
          (define reader-out (metadata-dump (read-file (path->string path))))
          (printf "  ~a: reader dump ~a ms\n" name (ms-since reader-start))
          (define diff (diff-summary reader-out (cdr srm-result)))
          (when diff
            (fail (string-append "reader dump differs from System.Reflection.Metadata: " diff)))])))
   (printf "corpus total: ~a ms\n" (ms-since corpus-start))]
  [else
   (oracle-missing "dotnet")])
