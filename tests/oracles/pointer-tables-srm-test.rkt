#lang racket/base
; Pointer-table images against System.Reflection.Metadata (tests/oracles/srm-dump). SRM follows
; MethodPtr, FieldPtr and ParamPtr, so for a #- image it must print the member ranges that Rangi's
; index returns. srm-dump prints each list as [first..last] only, so this compares endpoints. The
; full order is checked in tests/cli/pointer-tables-test.rkt.
(require rackunit racket/string
         "../lib/fixture.rkt" "../lib/patch-image.rkt" "../lib/srm.rkt"
         "../../src/cli-reader.rkt" "../../src/cli/index.rkt" "tools.rkt")

; "[first..last]" as srm-dump prints a list, or "[]" when it is empty
(define (range-text seq)
  (define rids (for/list ([r seq]) r))
  (if (null? rids)
      "[]"
      (format "[~a..~a]" (car rids) (car (reverse rids)))))

; the ranges srm-dump prints, keyed by (table row column)
(define (srm-ranges out)
  (for/fold ([h (hash)]) ([line (in-list (string-split out "\n"))])
    (define m (regexp-match #px"^  (TypeDef|MethodDef)\\[([0-9]+)\\] " line))
    (cond
      [(not m) h]
      [else
       (define table (cadr m))
       (define row (string->number (caddr m)))
       (define columns (if (equal? table "TypeDef") '("Fields" "Methods") '("Params")))
       (for/fold ([h h]) ([column (in-list columns)])
         (define v (regexp-match (pregexp (string-append column "=(\\[[0-9.]*\\])")) line))
         (if v (hash-set h (list table row column) (cadr v)) h))])))

; the same keys as srm-ranges, computed by Rangi's index
(define (reader-ranges rdr)
  (define (add h table row column seq)
    (hash-set h (list table row column) (range-text seq)))
  (define with-typedefs
    (for/fold ([h (hash)]) ([rid (in-range 1 (add1 (table-row-count rdr 'typedef)))])
      (add (add h "TypeDef" rid "Fields" (typedef-fields rdr rid))
           "TypeDef" rid "Methods" (typedef-methods rdr rid))))
  (for/fold ([h with-typedefs]) ([rid (in-range 1 (add1 (table-row-count rdr 'methoddef)))])
    (add h "MethodDef" rid "Params" (method-params rdr rid))))

; the first and last rid of an "[a..b]" range, or #f for "[]"
(define (endpoints v)
  (define m (regexp-match #px"^\\[([0-9]+)\\.\\.([0-9]+)\\]$" v))
  (and m (cons (string->number (cadr m)) (string->number (caddr m)))))

(cond
  [srm-dotnet
   (build-srm! srm-dotnet)
   (with-built-image
    "multi-types"
    (λ (dir exe)
      (define ptr-exe (build-path (current-directory) "pointers.exe"))
      (call-with-output-file ptr-exe
        (λ (o) (write-bytes (tilde->uncompressed (path->string exe)
                                                 #:pointer-tables '(methodptr fieldptr paramptr))
                            o))
        #:exists 'truncate)
      (define-values (base-code base-out base-err) (run-srm srm-dotnet exe))
      (define-values (ptr-code ptr-out ptr-err) (run-srm srm-dotnet ptr-exe))

      (test-case "srm-dump reads both images"
        (check-equal? base-code 0 base-err)
        (check-equal? ptr-code 0 ptr-err))

      (define srm-base (srm-ranges base-out))
      (define srm-ptr (srm-ranges ptr-out))
      (define reader (reader-ranges (read-file (path->string ptr-exe))))

      (test-case "reader ranges match srm-dump on the pointer image"
        (check-equal? (hash-count reader) (hash-count srm-ptr))
        (check-equal?
         (for/list ([(k v) (in-hash srm-ptr)]
                    #:unless (equal? (hash-ref reader k #f) v))
           (list k v (hash-ref reader k #f)))
         '()))

      (test-case "srm-dump sees each multi-row list reversed in the pointer image"
        (define reversed
          (for/list ([(k base) (in-hash srm-base)]
                     #:when (let ([e (endpoints base)]) (and e (not (= (car e) (cdr e))))))
            (list k base (hash-ref srm-ptr k))))
        (check-true (pair? reversed) "no multi-row lists in the fixture")
        (check-equal?
         (for/list ([r (in-list reversed)]
                    #:unless (let ([e (endpoints (cadr r))])
                               (equal? (caddr r) (format "[~a..~a]" (cdr e) (car e)))))
           r)
         '()))))]
  [else
   (oracle-missing "dotnet")])
