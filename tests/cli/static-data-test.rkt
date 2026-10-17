#lang racket/base
; Static data (II.16) and the FieldRVA table (II.22.18). A static field with a .data block gets a
; FieldRVA row whose RVA points at the block's chunk and whose Field column is the field's row.
; The field must be static and carry no Constant row.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/tables.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; A <Module> entry point, a Store class with the given fields, and top-level .data blocks.
(define (il-with store-fields data-forms)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) (ret) })])
     (.class (public auto ansi) Store [ ,@store-fields ])
     ,@data-forms)))

(define (store-fields cp)
  (define store
    (findf (λ (td) (equal? (tdef-name td) "Store")) (cli-program-typedefs cp)))
  (tdef-fields store))

(define table-data
  '((.field (public static) int32 Table at D_Table)
    (.field (public static) int32 Plain)))

(define table-block
  '(.data D_Table = (bytearray (01 00 00 00))))

(test-case "a static field with data gets the static and hasfieldrva flags and its own data"
  (define fs (store-fields (lower-module (il-with table-data (list table-block)))))
  ; Public | Static (II.23.1.5) | HasFieldRVA (II.22.18 flag, 0x0100)
  (check-equal? (fdef-flags (first fs)) #x0116)
  (check-equal? (fdef-data (first fs)) (bytes 1 0 0 0))
  ; the field without `at` has neither the flag nor data
  (check-equal? (fdef-flags (second fs)) #x16)
  (check-false (fdef-data (second fs))))

(test-case "a FieldRVA row names the field's rid and the RVA of its data chunk"
  (define cp (lower-module (il-with table-data (list table-block))))
  ; capture the table builder's rows through the #:extra hook, which runs after the program rows
  (define captured #f)
  (define mb
    (build-metadata cp "rangi-test" "rangi.dll"
                    #:extra (λ (tb sh bh) (set! captured tb))))
  (define rows (table-rows captured 'fieldrva))
  (check-equal? (map (λ (r) (cons (rva-ref-target (car r)) (cadr r))) rows)
                (list (cons (field-data-sym 1) 1)))
  ; the Table field is rid 1 (Store's first field); the Plain field has no FieldRVA row
  ; the RVA is a fixup into the data chunk, resolved by the image layout
  (check-not-false
   (findf (λ (f) (and (eq? (fixup-kind f) 'rva32)
                      (eq? (fixup-target f) (field-data-sym 1))))
          (chunk-fixups mb))))

(test-case "a FieldRVA field must be static"
  (check-exn exn:fail?
             (λ ()
               (lower-module
                (il-with '((.field (public) int32 Table at D_Table))
                         (list table-block))))))

(test-case "a literal field cannot also have data"
  (check-exn exn:fail?
             (λ ()
               (lower-module
                (il-with '((.field (public static literal) int32 Table = (int32 1) at D_Table))
                         (list table-block))))))

(test-case "a FieldRVA field must name existing data"
  (check-exn exn:fail?
             (λ ()
               (lower-module
                (il-with '((.field (public static) int32 Table at D_Missing))
                         (list table-block))))))

(test-case "the data length must match the field's primitive type"
  (check-exn exn:fail?
             (λ ()
               (il-with table-data
                        (list '(.data D_Table = (bytearray (01 00 00 00 02 00 00 00))))))))
