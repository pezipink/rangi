#lang racket/base
; Read-side checks on images that the fixtures assemble. The reader decodes the Assembly and
; AssemblyRef Flags (II.22.2, II.22.5), the FieldRVA rows (II.22.18) against the .sdata section
; (II.25.3), and every section header of the static-data image (II.25.3).
(require rackunit
         racket/file
         "../lib/fixture.rkt"
         "../../src/cli/reader.rkt"
         "../../src/pe/read.rkt")

(define (section-name h)
  (regexp-replace #rx#"\0+$" (hash-ref h 'name) #""))

(define (section-by-name hdrs name)
  (for/first ([h (in-list (hash-ref hdrs 'sec-headers))]
              #:when (equal? (section-name h) name))
    h))

(define (le-u32 b) (integer-bytes->integer b #f #f))
(define (section-va h) (le-u32 (hash-ref h 'virt-address)))
(define (section-vsize h) (le-u32 (hash-ref h 'virt-size)))

(test-case "the retargetable fixture reads back Assembly and AssemblyRef Flags 0x0100"
  (with-built-image
   "asm-refs-retargetable"
   (λ (dir exe)
     (define rdr (read-file exe))
     ; the Assembly row is the definition, and its Flags column is the sixth
     (check-equal? (vector-ref (read-row rdr 'assembly 1) 5) #x0100)
     ; mscorlib is the retargetable extern; System is not
     (check-equal? (vector-ref (read-row rdr 'assemblyref 1) 4) #x0100)
     (check-equal? (vector-ref (read-row rdr 'assemblyref 2) 4) 0))))

(test-case "the plain versioned fixture reads back AssemblyRef Flags 0"
  (with-built-image
   "asm-refs-versioned"
   (λ (dir exe)
     (define rdr (read-file exe))
     (check-equal? (vector-ref (read-row rdr 'assembly 1) 5) 0)
     (check-equal? (vector-ref (read-row rdr 'assemblyref 1) 4) 0)
     (check-equal? (vector-ref (read-row rdr 'assemblyref 2) 4) 0))))

(define (typedef-flags-by-name rdr name)
  (define n (table-data-row-count (hash-ref (asm-reader-table-attributes rdr) 'typedef)))
  (for/first ([rid (in-range 1 (add1 n))]
              #:when (equal? (vector-ref (read-row rdr 'typedef rid) 1) name))
    (vector-ref (read-row rdr 'typedef rid) 0)))

(test-case "static-data: TypeDef flags read back as TypeAttributes (II.22.37)"
  (with-built-image
   "static-data"
   (λ (dir exe)
     (define rdr (read-file exe))
     ; public Table has tdPublic (0x0001); private Program is NotPublic (0x0000)
     (check-equal? (typedef-flags-by-name rdr "Table") #x0001)
     (check-equal? (typedef-flags-by-name rdr "Program") #x0000))))

(test-case "static-data: FieldRVA rows point into .sdata at the bytes of their field's data"
  (with-built-image
   "static-data"
   (λ (dir exe)
     (define hdrs (call-with-input-file exe read-pe-headers))
     (define sdata (section-by-name hdrs #".sdata"))
     (check-true (and sdata #t) "image has an .sdata section")
     (define bs (file->bytes exe))
     (define rdr (read-file exe))
     ; the data blocks, keyed by the Field rid each FieldRVA row names
     ; (First = 1, Second = 3, Third = 4; Plain has no row)
     (define expected
       (list (cons 1 (bytes #x01 #x00 #x00 #x00))
             (cons 3 (bytes #x10 #x00 #x00 #x00))
             (cons 4 (bytes #x2A #x00 #x00 #x00))))
     (define rows
       (for/list ([rid (in-range 1 (add1 (length expected)))])
         (read-row rdr 'fieldrva rid)))
     (for ([row (in-list rows)] [want (in-list expected)])
       (define rva (vector-ref row 0))
       (check-equal? (vector-ref row 1) (car want) "FieldRVA names the field rid")
       (check-true (and (<= (section-va sdata) rva)
                        (< rva (+ (section-va sdata) (section-vsize sdata))))
                   (format "RVA 0x~x lies in .sdata" rva))
       (define off (rva->file-offset hdrs rva))
       (check-equal? (subbytes bs off (+ off 4)) (cdr want)
                     (format "bytes at RVA 0x~x match the field's data" rva))))))

(test-case "static-data: the reader sees every section of the image in header order"
  (with-built-image
   "static-data"
   (λ (dir exe)
     (define hdrs (call-with-input-file exe read-pe-headers))
     (check-equal? (map section-name (hash-ref hdrs 'sec-headers))
                   '(#".text" #".sdata" #".reloc"))
     (check-equal? (section-va (section-by-name hdrs #".text")) #x2000)
     (check-equal? (section-va (section-by-name hdrs #".sdata")) #x4000)
     (check-equal? (section-va (section-by-name hdrs #".reloc")) #x6000)
     ; each section's RVA maps to its own raw data
     (check-equal? (rva->file-offset hdrs #x4000)
                   (le-u32 (hash-ref (section-by-name hdrs #".sdata") 'ptr-raw))))))
