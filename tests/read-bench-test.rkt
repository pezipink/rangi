#lang racket/base
; Read-path baseline for the lazy reader. Opens the .NET 4.7.1 mscorlib reference assembly,
; checks its public top-level type count, and prints timings for the open and for enumerating
; the public types. Timings depend on the machine, so they are printed only and never asserted.
(require rackunit racket/list
         "../src/cli-reader.rkt" "oracles/tools.rkt")

; get-public-typedefs counts TypeDef rows whose visibility is Public (1). System.Reflection.Metadata
; (tests/oracles/srm-dump) reports the same 1520 for this file. The roadmap records 1521, which this
; file does not reproduce.
(define expected-public-count 1520)

(define iterations 20)

(define mscorlib
  (let ([dir (find-directory "RANGI_REFERENCE_ASSEMBLIES" net471-reference-dir)])
    (and dir
         (let ([p (build-path dir "mscorlib.dll")])
           (and (file-exists? p) (path->string p))))))

; runs the thunk once to warm the file cache, then iterations times; returns the sorted timings in ms
(define (time-runs thunk)
  (thunk)
  (sort (for/list ([_ (in-range iterations)])
          (define t0 (current-inexact-milliseconds))
          (thunk)
          (- (current-inexact-milliseconds) t0))
        <))

(define (summary times)
  (format "min ~a ms, median ~a ms, max ~a ms (n=~a)"
          (real->decimal-string (first times) 3)
          (real->decimal-string (list-ref times (quotient (length times) 2)) 3)
          (real->decimal-string (last times) 3)
          (length times)))

(cond
  [mscorlib
   (define open-times (time-runs (λ () (read-file mscorlib))))
   (define rdr (read-file mscorlib))
   (define enum-times (time-runs (λ () (get-public-typedefs rdr))))
   (define public-types (get-public-typedefs rdr))
   (printf "read-bench: mscorlib.dll (~a public types)\n" (length public-types))
   (printf "read-bench: lazy open (read-file): ~a\n" (summary open-times))
   (printf "read-bench: enumerate public types (get-public-typedefs): ~a\n" (summary enum-times))
   (test-case "mscorlib reference assembly has the baseline public type count"
     (check-equal? (length public-types) expected-public-count))]
  [else
   (printf "skipping read-bench: mscorlib.dll not found\n")])
