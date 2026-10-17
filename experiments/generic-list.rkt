#lang racket/base
; Demo: resolve List<int> from mscorlib by name, print its public members with int substituted,
; and time the lazy path. Run: racket experiments/generic-list.rkt
(require racket/list
         racket/promise
         (file "../src/types/canon.rkt")
         (file "../src/types/desc.rkt")
         (file "../src/types/provider.rkt")
         (file "../src/types/reference.rkt"))

(define mscorlib "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (ms s) (/ (round (* 1000 s)) 1000.0))

(define-values (rp open-ms) (let ([t (current-inexact-milliseconds)])
                              (values (open-reference-provider mscorlib)
                                      (- (current-inexact-milliseconds) t))))

(define e (make-env #:providers (list rp)
                    #:opens '("System" "System.Collections.Generic")))

(define (time-ms thunk)
  (define t (current-inexact-milliseconds))
  (define v (thunk))
  (values v (- (current-inexact-milliseconds) t)))

(define-values (open-list lookup-ms)
  (time-ms (λ () (resolve-type-name e #'List #:arity 1))))

(define int-ref (source-primitive "int"))
(define list-of-int (with-args open-list (list int-ref)))

(define-values (d desc-ms) (time-ms (λ () (env-type e list-of-int))))
(define-values (methods methods-ms)
  (time-ms (λ () (force (type-desc-methods d)))))

(printf "type:        ~a (~a)\n" (type->string list-of-int) (type-desc-shape d))
(printf "assembly:    ~a\n" (type-ref-asm open-list))
(printf "open:        ~a ms; resolve: ~a ms; closed descriptor: ~a ms; members: ~a ms\n"
        (ms open-ms) (ms lookup-ms) (ms desc-ms) (ms methods-ms))
(printf "\npublic instance members:\n")
(for ([m (in-list methods)] #:when (and (method-desc-public? m) (not (method-desc-static? m))))
  (printf "  ~a\n" (method->string m)))
(printf "\nfields:\n")
(for ([f (in-list (force (type-desc-fields d)))])
  (printf "  ~a ~a\n" (type->string (field-desc-type f)) (field-desc-name f)))

(printf "\nbase: ~a\n" (type->string (force (type-desc-base d))))
(printf "interfaces: ~a\n"
        (join-strings (map type->string (force (type-desc-interfaces d))) ", "))

(define enumerator-ref
  (method-desc-ret (findf (λ (m) (equal? (method-desc-name m) "GetEnumerator")) methods)))
(define enumerator (env-type e enumerator-ref))
(printf "\nnested ~a (~a), members from the outer type's arguments:\n"
        (type->string enumerator-ref) (type-desc-shape enumerator))
(for ([m (in-list (force (type-desc-methods enumerator)))] #:when (method-desc-public? m))
  (printf "  ~a\n" (method->string m)))

(define-values (chain chain-ms)
  (time-ms (λ () (find-methods e list-of-int "ToString"))))
(printf "\nToString reached through the base chain (~a ms):\n" (ms chain-ms))
(for ([m (in-list chain)]) (printf "  ~a\n" (method->string m)))

(printf "\nwarm lookups, 1000 x resolve + env-type of List<int>:\n")
(define-values (_ warm-ms)
  (time-ms (λ ()
             (for ([i (in-range 1000)])
               (env-type e (with-args (resolve-type-name e #'List #:arity 1) (list int-ref)))))))
(printf "  ~a µs per lookup\n" (/ (* 1000 warm-ms) 1000.0))
