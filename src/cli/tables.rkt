#lang racket/base
; CLI metadata tables (ECMA-335 II.22). Rows are added in the column order of schema.rkt
; and checked against it. sort-tables! orders the sorted tables and remaps every index
; into them, and tables-stream serialises the #~ stream (II.24.2.6).
(require racket/list
         "schema.rkt"
         "../private/binary.rkt")
(provide (struct-out rva-ref)
         make-tables
         add-row!
         table-row-count
         table-rows
         sort-tables!
         tables-stream)

; A 4-byte RVA cell (II.22.18, II.22.9). It is written as zero, and the caller patches it
; to the RVA of target at layout.
(struct rva-ref (target))

; counts: table name -> row count. rows: table name -> rows, newest first.
; sorted?: #t once sort-tables! has run since the last add-row!.
(struct tables (counts rows [sorted? #:mutable]))

(define (make-tables) (tables (make-hasheq) (make-hasheq) #f))

(define (table-row-count b name) (hash-ref (tables-counts b) name 0))

; rows of a table, oldest first; rids are 1-based positions in this list
(define (table-rows b name) (reverse (hash-ref (tables-rows b) name '())))

(define (check-cell name c v)
  (define kind (column-kind c))
  (define (fail)
    (error 'add-row! "~a.~a: bad value ~s for column kind ~a" name (column-name c) v kind))
  (cond
    [(and (rva-ref? v) (eq? (column-name c) 'rva)) (void)]
    [(not (exact-nonnegative-integer? v)) (fail)]
    [(memq kind '(u8 u16 u32))
     (unless (< v (expt 2 (case kind [(u8) 8] [(u16) 16] [else 32]))) (fail))]
    [else (void)]))

; Adds one row and returns its rid. Values are in the column order of the table.
(define (add-row! b name . values)
  (define t (or (table-by-name name) (error 'add-row! "unknown table ~a" name)))
  (define cols (table-columns t))
  (unless (= (length values) (length cols))
    (error 'add-row! "~a takes ~a columns, got ~a" name (length cols) (length values)))
  (for ([v (in-list values)] [c (in-list cols)]) (check-cell name c v))
  (hash-set! (tables-rows b) name (cons values (hash-ref (tables-rows b) name '())))
  (define rid (add1 (table-row-count b name)))
  (hash-set! (tables-counts b) name rid)
  (set-tables-sorted?! b #f)
  rid)

; ---------------------------------------------------------------------------
; sorting

; true when a coded or simple index in kind points into a sorted table
(define (sorted-target? kind)
  (define (sorted-name? n) (table-sorted (table-by-name n)))
  (and (pair? kind)
       (case (car kind)
         [(index) (and (sorted-name? (cadr kind)) #t)]
         [(coded) (for/or ([t (in-vector (coded-kind-targets (coded-kind-by-name (cadr kind))))])
                    (and t (sorted-name? t) #t))]
         [else #f])))

; Sorts every present table that has a sort key by that key, then remaps every index into
; a sorted table. A sort key may point into another sorted table; such tables are sorted
; after their targets, and a cycle is an error.
(define (sort-tables! b)
  (define maps (make-hasheq))    ; sorted table name -> vector, old rid -> new rid
  (define ordered (make-hasheq)) ; sorted table name -> rows in sorted order, oldest first

  (define (remap-rid name rid)
    (define m (hash-ref maps name #f))
    (if m (vector-ref m rid) rid))

  ; a row's index value, with a coded index rewritten to the target's new rid. Null stays null.
  (define (remap-value kind v)
    (cond
      [(not (exact-nonnegative-integer? v)) v]
      [(and (pair? kind) (eq? (car kind) 'index)) (remap-rid (cadr kind) v)]
      [(and (pair? kind) (eq? (car kind) 'coded))
       (define-values (target rid) (coded-decode (coded-kind-by-name (cadr kind)) v))
       (if (and target (> rid 0) (hash-ref maps target #f))
           (coded-encode (cadr kind) target (remap-rid target rid))
           v)]
      [else v]))

  (define (present-sorted-tables)
    (for/list ([t (in-list schema-tables)]
               #:when (and (table-sorted t) (positive? (table-row-count b (table-name t)))))
      t))

  (define (key-targets-ready? t)
    (define kind (column-kind (findf (λ (c) (eq? (column-name c) (table-sorted t)))
                                     (table-columns t))))
    (for/and ([n (in-list (key-target-names kind))])
      (or (zero? (table-row-count b n)) (hash-ref maps n #f))))

  (define (key-target-names kind)
    (cond
      [(not (sorted-target? kind)) '()]
      [(eq? (car kind) 'index) (list (cadr kind))]
      [else (for/list ([t (in-vector (coded-kind-targets (coded-kind-by-name (cadr kind))))]
                       #:when (and t (table-sorted (table-by-name t))))
              t)]))

  (define (sort-one! t)
    (define name (table-name t))
    (define cols (table-columns t))
    (define key-idx (index-where cols (λ (c) (eq? (column-name c) (table-sorted t)))))
    (define key-kind (column-kind (list-ref cols key-idx)))
    (define keyed
      (sort (for/list ([r (in-list (table-rows b name))] [rid (in-naturals 1)])
              (list (remap-value key-kind (list-ref r key-idx)) rid r))
            < #:key car))
    (define new-of (make-vector (add1 (length keyed)) 0))
    (for ([k (in-list keyed)] [new (in-naturals 1)])
      (vector-set! new-of (cadr k) new))
    (hash-set! maps name new-of)
    (hash-set! ordered name (map caddr keyed)))

  (let loop ([pending (present-sorted-tables)])
    (unless (null? pending)
      (define-values (ready later) (partition key-targets-ready? pending))
      (when (null? ready)
        (error 'sort-tables! "sort keys form a cycle through ~a" (map table-name pending)))
      (for-each sort-one! ready)
      (loop later)))

  ; every row now holds new rids, so rewrite every table in one pass
  (for ([t (in-list schema-tables)] #:when (positive? (table-row-count b (table-name t))))
    (define name (table-name t))
    (define cols (table-columns t))
    (define rows (hash-ref ordered name (λ () (table-rows b name))))
    (hash-set! (tables-rows b) name
               (reverse
                (for/list ([row (in-list rows)])
                  (for/list ([v (in-list row)] [c (in-list cols)])
                    (remap-value (column-kind c) v))))))
  (set-tables-sorted?! b #t))

; ---------------------------------------------------------------------------
; #~ stream

; The stream header (II.24.2.6) is reserved, version 2.0, HeapSizes, reserved, Valid, Sorted.
; Heap index widths come from the caller, who knows the heap sizes.
; Returns the stream bytes and the RVA fixups as (offset . target), relative to the stream.
(define (tables-stream b #:string-wide? sw #:blob-wide? bw #:guid-wide? gw)
  (define present
    (for/list ([t (in-list (sort schema-tables < #:key table-id))]
               #:when (positive? (table-row-count b (table-name t))))
      t))
  (when (and (not (tables-sorted? b)) (ormap table-sorted present))
    (error 'tables-stream "sorted tables need sort-tables! before serialising"))
  (define (rows-of name) (table-row-count b name))
  (define (width kind)
    (column-width kind (if sw 4 2) (if bw 4 2) (if gw 4 2) rows-of))

  (define valid (for/sum ([t (in-list present)]) (arithmetic-shift 1 (table-id t))))
  (define sorted-mask
    (for/sum ([t (in-list present)] #:when (table-sorted t)) (arithmetic-shift 1 (table-id t))))
  (define heap-flags (+ (if sw 1 0) (if gw 2 0) (if bw 4 0)))
  (define header
    (bytes-append (le 0 4) (bytes 2 0 heap-flags 1) (le valid 8) (le sorted-mask 8)))
  (define counts
    (apply bytes-append (for/list ([t (in-list present)]) (le (rows-of (table-name t)) 4))))
  (define body-start (+ (bytes-length header) (bytes-length counts)))

  (define cells
    (for*/list ([t (in-list present)]
                [row (in-list (table-rows b (table-name t)))]
                [(v c) (in-parallel row (table-columns t))])
      (cons v (width (column-kind c)))))
  (define-values (body fixups)
    (let loop ([cs cells] [pos body-start] [parts '()] [fx '()])
      (cond
        [(null? cs) (values (apply bytes-append (reverse parts)) (reverse fx))]
        [else
         (define v (caar cs))
         (define w (cdar cs))
         (if (rva-ref? v)
             (loop (cdr cs) (+ pos w) (cons (make-bytes w 0) parts)
                   (cons (cons pos (rva-ref-target v)) fx))
             (loop (cdr cs) (+ pos w) (cons (le v w) parts) fx))])))
  (values (pad-to (bytes-append header counts body) 4) fixups))
