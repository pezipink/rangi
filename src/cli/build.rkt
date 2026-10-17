#lang racket/base
(require racket/match
         racket/list
         "lower.rkt"
         "schema.rkt"
         "heaps.rkt"
         "tables.rkt"
         "metadata.rkt"
         "../private/binary.rkt")
(provide build-metadata method-sym)

(define (method-sym i) (string->symbol (format "method:~a" i)))

; starts-of: 1-based first rid of each owner's run of rows (MethodList, FieldList)
(define (starts-of counts)
  (let loop ([cs counts] [next 1] [acc '()])
    (if (null? cs)
        (reverse acc)
        (loop (cdr cs) (+ next (car cs)) (cons next acc)))))

; Adds the rows, sorts, and serialises the heaps and the #~ stream. The MVID is a
; zero placeholder in #GUID, filled at layout by the digest in metadata-chunk.
(define (build-metadata p asm-name mod-name)
  (define tb (make-tables))
  (define sh (make-strings-heap))
  (define bh (make-blob-heap))
  (define gh (make-guid-heap))
  (define uh (cli-program-us-heap p))
  (define (s x) (heap-add! sh x))
  (define (b x) (heap-add! bh x))
  (define tds (cli-program-typedefs p))
  (define mdefs (append-map tdef-methods tds))
  (define starts (starts-of (map (λ (td) (length (tdef-methods td))) tds)))
  (define mvid (heap-add! gh (make-bytes 16 0)))
  (add-row! tb 'module 0 (s mod-name) mvid 0 0)
  (for ([r (in-list (cli-program-typerefs p))])
    (match-let ([(list asm ns name) r])
      (add-row! tb 'typeref (coded-encode 'resolutionscope 'assemblyref asm) (s name) (s ns))))
  (for ([td (in-list tds)] [start (in-list starts)])
    (define ext (tdef-extends td))
    (add-row! tb 'typedef (tdef-flags td) (s (tdef-name td)) (s (tdef-ns td))
              (if ext (coded-encode 'typedeforref 'typeref ext) 0)
              1
              start))
  (for ([m (in-list mdefs)] [i (in-naturals)])
    (add-row! tb 'methoddef (rva-ref (method-sym i)) 0 (mdef-flags m) (s (mdef-name m))
              (b (mdef-sig m)) 1))
  (for ([r (in-list (cli-program-memberrefs p))])
    (match-let ([(list tr name sig) r])
      (add-row! tb 'memberref (coded-encode 'memberrefparent 'typeref tr) (s name) (b sig))))
  (for ([sig (in-list (cli-program-standalone-sigs p))])
    (add-row! tb 'standalonesig (b sig)))
  (add-row! tb 'assembly 0 0 0 0 0 0 0 (s asm-name) 0)
  (for ([n (in-list (cli-program-asm-refs p))])
    (add-row! tb 'assemblyref 0 0 0 0 0 0 (s n) 0 0))

  (sort-tables! tb)
  (define strs (pad-to (heap-serialise sh) 4))
  (define blobs (pad-to (heap-serialise bh) 4))
  (define-values (tilde table-fixups)
    (tables-stream tb
                   #:string-wide? (> (bytes-length strs) #xFFFF)
                   #:blob-wide? (> (bytes-length blobs) #xFFFF)
                   #:guid-wide? #f))
  (metadata-chunk (list (cons "#~" tilde)
                        (cons "#Strings" strs)
                        (cons "#US" (pad-to (heap-serialise uh) 4))
                        (cons "#GUID" (heap-serialise gh))
                        (cons "#Blob" blobs))
                  #:table-fixups table-fixups
                  #:mvid-index mvid))
