#lang racket/base
; Row helpers for TypeSpec, MethodSpec, StandAloneSig, GenericParam and GenericParamConstraint,
; and the owner-order sort of the generic tables (ECMA-335 II.22.20, II.22.21, II.24.2.6).
(require rackunit
         "../../src/cli/schema.rkt"
         "../../src/cli/tables.rkt"
         "../../src/cli/heaps.rkt"
         "../../src/cli/build.rkt")

(test-case "signature rows point at blob heap entries and return 1-based rids"
  (define tb (make-tables))
  (define bh (make-blob-heap))
  (define sig (bytes #x1D #x12 #x09))
  (check-equal? (add-typespec-row! tb bh sig) 1)
  (check-equal? (add-standalonesig-row! tb bh (bytes #x07 #x00)) 1)
  (check-equal? (table-row-count tb 'typespec) 1)
  (check-equal? (table-row-count tb 'standalonesig) 1)
  ; the blob heap dedups, so adding the same bytes again returns the same index
  (check-equal? (car (car (table-rows tb 'typespec))) (heap-add! bh sig)))

(test-case "MethodSpec method column is a methoddeforref coded index"
  (define tb (make-tables))
  (define bh (make-blob-heap))
  (add-methodspec-row! tb bh (cons 'memberref 2) (bytes #x0A #x01 #x08))
  (add-methodspec-row! tb bh (cons 'methoddef 3) (bytes #x0A #x01 #x08))
  ; memberref 2: (2 << 1) | 1 = 5; methoddef 3: (3 << 1) | 0 = 6
  (check-equal? (map car (table-rows tb 'methodspec)) '(5 6)))

(test-case "GenericParam and GenericParamConstraint are sorted by owner with remapped indexes"
  (define tb (make-tables))
  (define sh (make-strings-heap))
  (define bh (make-blob-heap))
  ; typeormethoddef coded values (1-bit tag): typedef 1 = 2, methoddef 1 = 3, typedef 2 = 4
  ; rows are inserted in the order B, C, A, so the sort moves A to rid 1, B to 2, C to 3
  (define gp-b (add-genericparam-row! tb sh 0 0 (cons 'methoddef 1) "B"))
  (define gp-c (add-genericparam-row! tb sh 0 0 (cons 'typedef 2) "C"))
  (define gp-a (add-genericparam-row! tb sh 0 0 (cons 'typedef 1) "A"))
  (check-equal? (list gp-b gp-c gp-a) '(1 2 3))
  ; constraints point at the pre-sort rids of their GenericParam rows
  (add-genericparamconstraint-row! tb gp-b (cons 'typedef 5))
  (add-genericparamconstraint-row! tb gp-a (cons 'typeref 2))
  (sort-tables! tb)
  (check-equal? (map caddr (table-rows tb 'genericparam)) (list 2 3 4))
  ; constraint owners are remapped: gp-a 3 -> 1, gp-b 1 -> 2
  ; typeref 2 coded (2 << 2) | 1 = 9; typedef 5 coded (5 << 2) | 0 = 20
  (check-equal? (table-rows tb 'genericparamconstraint) (list (list 1 9) (list 2 20))))

(test-case "sorted mask has the GenericParam (0x2A) and GenericParamConstraint (0x2C) bits"
  (define tb (make-tables))
  (define sh (make-strings-heap))
  (define bh (make-blob-heap))
  (define gp (add-genericparam-row! tb sh 0 0 (cons 'typedef 1) "T"))
  (add-genericparamconstraint-row! tb gp (cons 'typedef 1))
  (sort-tables! tb)
  (define-values (bs fx) (tables-stream tb #:string-wide? #f #:blob-wide? #f #:guid-wide? #f))
  ; sorted mask is the 8 bytes at offset 16; bits 42 and 44 are byte 5, bits 2 and 4: 0x04 + 0x10
  (check-equal? (subbytes bs 16 24) (bytes 0 0 0 0 0 #x14 0 0)))
