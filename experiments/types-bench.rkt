#lang racket/base
; Times the types layer against the budgets in docs/plans/types.md, on the .NET 4.7.1 mscorlib
; reference assembly. Run: racket experiments/types-bench.rkt. Timings depend on the machine, so
; they are printed only, never asserted.
(require racket/list
         racket/promise
         (file "../src/types/canon.rkt")
         (file "../src/types/desc.rkt")
         (file "../src/types/provider.rkt")
         (file "../src/types/reference.rkt"))

(define mscorlib
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define iterations 20)

(define (summary times [unit "ms"])
  (define sorted (sort times <))
  (format "min ~a, median ~a, max ~a ~a (n=~a)"
          (real->decimal-string (first sorted) 3)
          (real->decimal-string (list-ref sorted (quotient (length sorted) 2)) 3)
          (real->decimal-string (last sorted) 3)
          unit
          (length sorted)))

; One timing of thunk, in ms. setup runs first and is not timed, so each run starts from the same state.
(define (time-once setup thunk)
  (define x (setup))
  (define t (current-inexact-milliseconds))
  (thunk x)
  (- (current-inexact-milliseconds) t))

(define (times setup thunk)
  (for/list ([_ (in-range iterations)]) (time-once setup thunk)))

(define string-ref (type-ref "mscorlib" "System" "String" 0 'class '()))

(printf "types-bench: mscorlib.dll, ~a runs each\n" iterations)

(printf "open a reference provider: ~a\n"
        (summary (times void (λ (_) (open-reference-provider mscorlib)))))

(printf "open + first lookup of System.String (cold): ~a\n"
        (summary (times void
                        (λ (_)
                          (define e (make-env #:providers (list (open-reference-provider mscorlib))))
                          (env-type e (lookup-type e "System" "String" 0))))))

; Warm: the reference is already cached in the env, so only the cache hit is timed.
(define warm-env (make-env #:providers (list (open-reference-provider mscorlib))))
(void (env-type warm-env (lookup-type warm-env "System" "String" 0)))
(define warm-calls 1000)
(printf "warm lookup of a cached reference, per call (µs): ~a\n"
        (summary (for/list ([ms (in-list (times void (λ (_) (for ([_ (in-range warm-calls)])
                                                              (env-type warm-env string-ref)))))])
                   (/ (* 1000 ms) warm-calls))
                 "µs"))

; Members: a fresh env for each run, so the signatures are decoded again every time.
(define member-provider (open-reference-provider mscorlib))
(define member-count
  (let ([e (make-env #:providers (list member-provider))])
    (define s (env-type e (lookup-type e "System" "String" 0)))
    (+ (length (force (type-desc-methods s))) (length (force (type-desc-fields s))))))
(printf "members decoded for System.String (~a methods and fields): ~a\n"
        member-count
        (summary (times (λ () (make-env #:providers (list member-provider)))
                        (λ (e)
                          (define s (env-type e (lookup-type e "System" "String" 0)))
                          (force (type-desc-methods s))
                          (force (type-desc-fields s))))))
