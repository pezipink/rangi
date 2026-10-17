#lang racket/base
(require racket/match
         racket/list
         "lower.rkt"
         "schema.rkt"
         "heaps.rkt"
         "tables.rkt"
         "metadata.rkt"
         "../private/binary.rkt")
(provide build-metadata method-sym
         add-typespec-row! add-standalonesig-row! add-methodspec-row!
         add-genericparam-row! add-genericparamconstraint-row!)

(define (method-sym i) (string->symbol (format "method:~a" i)))

; Row helpers for the generics and signature tables. Each takes the table builder and the
; heaps it writes into, and returns the 1-based rid. A target is (cons table rid).
; Sorting is left to sort-tables!, which keeps GenericParam and GenericParamConstraint
; in owner order.
(define (add-typespec-row! tb bh sig)
  (add-row! tb 'typespec (heap-add! bh sig)))

(define (add-standalonesig-row! tb bh sig)
  (add-row! tb 'standalonesig (heap-add! bh sig)))

; method is (cons 'methoddef rid) or (cons 'memberref rid)
(define (add-methodspec-row! tb bh method inst)
  (add-row! tb 'methodspec (coded-encode 'methoddeforref (car method) (cdr method))
            (heap-add! bh inst)))

; owner is (cons 'typedef rid) or (cons 'methoddef rid)
(define (add-genericparam-row! tb sh number flags owner name)
  (add-row! tb 'genericparam number flags
            (coded-encode 'typeormethoddef (car owner) (cdr owner))
            (heap-add! sh name)))

; owner is the rid of a GenericParam row; constraint is (cons 'typedef|'typeref|'typespec rid)
(define (add-genericparamconstraint-row! tb owner constraint)
  (add-row! tb 'genericparamconstraint owner
            (coded-encode 'typedeforref (car constraint) (cdr constraint))))

; starts-of: 1-based first rid of each owner's run of rows (MethodList, FieldList)
(define (starts-of counts)
  (let loop ([cs counts] [next 1] [acc '()])
    (if (null? cs)
        (reverse acc)
        (loop (cdr cs) (+ next (car cs)) (cons next acc)))))

; Adds the rows, sorts, and serialises the heaps and the #~ stream. The MVID is a
; zero placeholder in #GUID, filled at layout by the digest in metadata-chunk.
; extra is called with (tb sh bh) after the program rows and before sorting, so tests can add
; generics rows that the program model does not produce yet.
(define (build-metadata p asm-name mod-name #:extra [extra (λ (tb sh bh) (void))])
  (define tb (make-tables))
  (define sh (make-strings-heap))
  (define bh (make-blob-heap))
  (define gh (make-guid-heap))
  (define uh (or (cli-program-us-heap p) (make-us-heap)))
  (define (s x) (heap-add! sh x))
  (define (b x) (heap-add! bh x))
  (define tds (cli-program-typedefs p))
  (define mdefs (append-map tdef-methods tds))
  (define starts (starts-of (map (λ (td) (length (tdef-methods td))) tds)))
  (define field-starts (starts-of (map (λ (td) (length (tdef-fields td))) tds)))
  (define mvid (heap-add! gh (make-bytes 16 0)))
  (add-row! tb 'module 0 (s mod-name) mvid 0 0)
  (for ([r (in-list (cli-program-typerefs p))])
    (match-let ([(list asm ns name) r])
      (add-row! tb 'typeref (coded-encode 'resolutionscope 'assemblyref asm) (s name) (s ns))))
  (for ([td (in-list tds)] [fstart (in-list field-starts)] [start (in-list starts)])
    (define ext (tdef-extends td))
    (add-row! tb 'typedef (tdef-flags td) (s (tdef-name td)) (s (tdef-ns td))
              (if ext (coded-encode 'typedeforref 'typeref ext) 0)
              fstart
              start))
  (for ([f (in-list (append-map tdef-fields tds))])
    (add-row! tb 'field (fdef-flags f) (s (fdef-name f)) (b (fdef-sig f))))
  (for ([m (in-list mdefs)] [i (in-naturals)])
    (add-row! tb 'methoddef (rva-ref (method-sym i)) 0 (mdef-flags m) (s (mdef-name m))
              (b (mdef-sig m)) 1))
  (for ([r (in-list (cli-program-memberrefs p))])
    (match-let ([(list parent name sig) r])
      (add-row! tb 'memberref (coded-encode 'memberrefparent (car parent) (cdr parent))
                (s name) (b sig))))
  (for ([blob (in-list (cli-program-typespecs p))])
    (add-typespec-row! tb bh blob))
  (for ([ms (in-list (cli-program-methodspecs p))])
    (match-let ([(list method inst) ms])
      (add-methodspec-row! tb bh method inst)))
  (for ([gp (in-list (cli-program-genericparams p))])
    (match-let ([(list number name owner) gp])
      (add-genericparam-row! tb sh number 0 owner name)))
  (for ([sig (in-list (cli-program-standalone-sigs p))])
    (add-row! tb 'standalonesig (b sig)))
  (add-row! tb 'assembly 0 0 0 0 0 0 0 (s asm-name) 0)
  (for ([n (in-list (cli-program-asm-refs p))])
    (add-row! tb 'assemblyref 0 0 0 0 0 0 (s n) 0 0))

  (extra tb sh bh)
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
