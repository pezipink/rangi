#lang racket/base
; Tests for the metadata table store: schema-checked rows, sorting with index remap, and the
; #~ stream header and RVA fixups (ECMA-335 II.22, II.24.2.6).
(require rackunit
         "../../src/cli/schema.rkt"
         "../../src/cli/tables.rkt")

(define (stream b)
  (define-values (bs fx)
    (tables-stream b #:string-wide? #f #:blob-wide? #f #:guid-wide? #f))
  (values bs fx))

; ---------------------------------------------------------------------------
; add-row! checks

(test-case "add-row! returns 1-based rids in insertion order"
  (define b (make-tables))
  (check-equal? (add-row! b 'typeref (coded-encode 'resolutionscope 'module 1) 1 2) 1)
  (check-equal? (add-row! b 'typeref (coded-encode 'resolutionscope 'module 1) 3 4) 2)
  (check-equal? (table-row-count b 'typeref) 2))

(test-case "add-row! rejects the wrong number of columns"
  (define b (make-tables))
  (check-exn exn:fail? (λ () (add-row! b 'module 1))))

(test-case "add-row! rejects an unknown table"
  (define b (make-tables))
  (check-exn exn:fail? (λ () (add-row! b 'nosuchtable 1))))

(test-case "add-row! rejects a value that overflows its column"
  (define b (make-tables))
  ; typedef.flags is u32, so 2^32 is out of range; a 16-bit column is checked the same way
  (check-exn exn:fail? (λ () (add-row! b 'typedef (expt 2 32) 0 0 0 0 0)))
  (check-exn exn:fail? (λ () (add-row! b 'module (expt 2 16) 0 0 0)))
  (check-exn exn:fail? (λ () (add-row! b 'methoddef 0 (expt 2 16) 0 0 0 1))))

(test-case "rva-ref is only accepted in the rva column"
  (define b (make-tables))
  (check-exn exn:fail? (λ () (add-row! b 'typedef (rva-ref 'x) 0 0 0 0 0)))
  (check-equal? (add-row! b 'methoddef (rva-ref 'x) 0 0 0 0 1) 1))

; ---------------------------------------------------------------------------
; #~ stream header and fixups

(test-case "stream header has version 2.0, Valid bit for the present table and no Sorted bits"
  (define b (make-tables))
  (add-row! b 'methoddef (rva-ref 'm0) 0 0 0 0 1)
  (define-values (bs fx) (stream b))
  (check-equal? (subbytes bs 4 8) (bytes 2 0 0 1))
  (check-equal? (subbytes bs 8 16) (bytes 64 0 0 0 0 0 0 0) "Valid bit 6 is 0x40")
  (check-equal? (subbytes bs 16 24) (bytes 0 0 0 0 0 0 0 0)))

(test-case "a single methoddef RVA fixup lands on the first byte of its row"
  (define b (make-tables))
  (add-row! b 'methoddef (rva-ref 'm0) 0 0 0 0 1)
  (define-values (bs fx) (stream b))
  ; 24-byte header, one 4-byte row count, then the row whose first column is the RVA
  (check-equal? fx (list (cons 28 'm0)))
  (check-equal? (subbytes bs 28 32) (bytes 0 0 0 0)))

(test-case "stream without rva-ref cells has no fixups"
  (define b (make-tables))
  (add-row! b 'module 0 0 0 0 0)
  (define-values (bs fx) (stream b))
  (check-equal? fx '()))

(test-case "tables-stream rejects sorted tables before sort-tables!"
  (define b (make-tables))
  (add-row! b 'interfaceimpl 1 (coded-encode 'typedeforref 'typedef 1))
  (check-exn exn:fail? (λ () (stream b))))

; ---------------------------------------------------------------------------
; sorting and index remap

(test-case "sort-tables! orders interfaceimpl by its class index"
  (define b (make-tables))
  (add-row! b 'interfaceimpl 2 (coded-encode 'typedeforref 'typedef 1))
  (add-row! b 'interfaceimpl 1 (coded-encode 'typedeforref 'typeref 1))
  (sort-tables! b)
  (check-equal? (table-rows b 'interfaceimpl)
                (list (list 1 (coded-encode 'typedeforref 'typeref 1))
                      (list 2 (coded-encode 'typedeforref 'typedef 1)))))

(test-case "sort-tables! remaps the index of a row in another sorted table"
  (define b (make-tables))
  ; genericparam is keyed by its coded owner: methoddef 1 (key 3) sorts after typedef 1 (key 2)
  (add-row! b 'genericparam 0 0 (coded-encode 'typeormethoddef 'methoddef 1) 0)
  (add-row! b 'genericparam 0 0 (coded-encode 'typeormethoddef 'typedef 1) 0)
  ; genericparamconstraint is keyed by its owner index into genericparam
  (add-row! b 'genericparamconstraint 1 (coded-encode 'typedeforref 'typedef 5))
  (add-row! b 'genericparamconstraint 2 (coded-encode 'typedeforref 'typedef 6))
  (sort-tables! b)
  (define gp (table-rows b 'genericparam))
  (check-equal? (map caddr gp)
                (list (coded-encode 'typeormethoddef 'typedef 1)
                      (coded-encode 'typeormethoddef 'methoddef 1)))
  ; the constraint owned by old rid 2 now owns new rid 1, and comes first
  (check-equal? (table-rows b 'genericparamconstraint)
                (list (list 1 (coded-encode 'typedeforref 'typedef 6))
                      (list 2 (coded-encode 'typedeforref 'typedef 5)))))

(test-case "sorted mask marks the sorted tables after sort-tables!"
  (define b (make-tables))
  (add-row! b 'interfaceimpl 1 (coded-encode 'typedeforref 'typedef 1))
  (add-row! b 'methoddef (rva-ref 'm0) 0 0 0 0 1)
  (sort-tables! b)
  (define-values (bs fx) (stream b))
  (define valid (+ (arithmetic-shift 1 9) (arithmetic-shift 1 6)))
  (check-equal? (subbytes bs 8 16)
                (bytes (bitwise-and valid 255) (arithmetic-shift valid -8) 0 0 0 0 0 0))
  (check-equal? (subbytes bs 16 24) (bytes 0 2 0 0 0 0 0 0)))
