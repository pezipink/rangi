#lang racket/base
; Pointer tables (II.22.37 MethodPtr and friends, II.24.2.6 #- streams). The multi-types fixture
; is patched to a #- image with MethodPtr, FieldPtr and ParamPtr rows. Each owner's run is reversed
; in the pointer tables, so the reader must return every member list in reverse of the #~ list,
; with the same owners, and the image must still run.
(require rackunit racket/file
         "../lib/fixture.rkt" "../lib/patch-image.rkt"
         "../../src/cli-reader.rkt" "../../src/cli/index.rkt")

(define (member-lists rdr owner-table lister)
  (for/list ([rid (in-range 1 (add1 (table-row-count rdr owner-table)))])
    (for/list ([m (lister rdr rid)]) m)))

(define (owners rdr owner-table member-table owner-of)
  (for/list ([m (in-range 1 (add1 (table-row-count rdr member-table)))])
    (owner-of rdr m)))

(with-built-image
 "multi-types"
 (λ (dir exe)
   (define ptr-exe (build-path (current-directory) "pointers.exe"))
   (call-with-output-file ptr-exe
     (λ (o) (write-bytes (tilde->uncompressed (path->string exe)
                                              #:pointer-tables '(methodptr fieldptr paramptr))
                         o))
     #:exists 'truncate)
   (define base (read-file (path->string exe)))
   (define ptr (read-file (path->string ptr-exe)))

   (test-case "pointer tables hold one row per target row"
     (check-equal? (table-row-count ptr 'methodptr) (table-row-count base 'methoddef))
     (check-equal? (table-row-count ptr 'fieldptr) (table-row-count base 'field))
     (check-equal? (table-row-count ptr 'paramptr) (table-row-count base 'param)))

   (test-case "member lists are the #~ lists reversed"
     (define method-lists (member-lists base 'typedef typedef-methods))
     (check-true (for/or ([l (in-list method-lists)]) (> (length l) 1)))
     (check-equal? (member-lists ptr 'typedef typedef-methods) (map reverse method-lists))
     (define field-lists (member-lists base 'typedef typedef-fields))
     (check-equal? (member-lists ptr 'typedef typedef-fields) (map reverse field-lists))
     (define param-lists (member-lists base 'methoddef method-params))
     (check-equal? (member-lists ptr 'methoddef method-params) (map reverse param-lists)))

   (test-case "owners are the same as in the #~ image"
     (check-equal? (owners ptr 'typedef 'methoddef method-owner)
                   (owners base 'typedef 'methoddef method-owner))
     (check-equal? (owners ptr 'typedef 'field field-owner)
                   (owners base 'typedef 'field field-owner)))

   (test-case "pointer image runs"
     (define-values (status stdout) (run-image ptr-exe))
     (check-equal? status 0 "exit status")
     (check-equal? (normalize-newlines stdout)
                   (normalize-newlines (file->string (build-path dir "expected-stdout.txt")))))))
