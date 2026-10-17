#lang racket/base
; Read-path baseline for the lazy reader. Opens the .NET 4.7.1 mscorlib reference assembly,
; checks its public top-level type count, and prints timings for the open, for building each
; cached index on a fresh reader (cold), and for lookups against a reader that has them (warm). Timings depend on the machine, so they are printed only and never asserted.
(require rackunit racket/list
         "../src/cli-reader.rkt" "../src/cli/index.rkt" "oracles/tools.rkt")

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
   ; cold timings include the open, so subtract the open line to get the index build alone
   (define enum-times (time-runs (λ () (get-public-typedefs (read-file mscorlib)))))
   (define index-times (time-runs (λ () (find-typedef (read-file mscorlib) "System" "String"))))
   (define public-types (get-public-typedefs rdr))
   (define string-rid (find-typedef rdr "System" "String"))
   (define lookup-times
     (time-runs (λ () (for ([_ (in-range 1000)]) (find-typedef rdr "System" "String")))))
   (define member-times
     (time-runs (λ ()
                  (define-values (s e) (typedef-methods rdr string-rid))
                  (for ([m (in-range s e)]) (row-column rdr 'methoddef m 'name)))))
   (define iface-times
     (time-runs (λ () (for ([_ (in-range 1000)]) (interface-impls rdr string-rid)))))
   (printf "read-bench: mscorlib.dll (~a public types)\n" (length public-types))
   (printf "read-bench: lazy open (read-file): ~a\n" (summary open-times))
   (printf "read-bench: open + enumerate public types, cold: ~a\n" (summary enum-times))
   (printf "read-bench: open + first find-typedef (builds name index), cold: ~a\n"
           (summary index-times))
   (printf "read-bench: 1000 find-typedef, warm: ~a\n" (summary lookup-times))
   (printf "read-bench: names of String's methods: ~a\n" (summary member-times))
   (printf "read-bench: 1000 interface-impls (binary search): ~a\n" (summary iface-times))
   (test-case "mscorlib reference assembly has the baseline public type count"
     (check-equal? (length public-types) expected-public-count))]
  [else
   (printf "skipping read-bench: mscorlib.dll not found\n")])
