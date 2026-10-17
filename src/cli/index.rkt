#lang racket/base
; Lookup indexes over a reader's metadata tables, for type systems running at phase 1.
;
; Speed rules, because the macro expander (and DrRacket's background expansion, on every edit)
; calls these constantly:
;  * Nothing is computed when an image is opened. Each index is built on first use and cached on
;    the reader (asm-reader-cache), so it lives exactly as long as the reader.
;  * Tables the spec keeps sorted (II.22, the Sorted mask of II.24.2.6) are binary searched in
;    place and need no index. A hash is built only for lookups the sort order does not serve, or
;    when an image does not mark the table sorted.
;  * Hot loops read integers straight from the raw bytes and do not allocate.
;  * Ranges are returned as two values, start and end (exclusive), for use with in-range.
;
; Lists come back in row order. The hashes are only looked up, never iterated for output.
; Images with the pointer tables (MethodPtr and friends, II.24.2.6 #- streams) are not handled:
; ranges index the member tables directly.
(require "reader.rkt" "schema.rkt")
(provide find-typedef find-exported-type
         typedef-methods typedef-fields method-params method-owner field-owner
         nested-types enclosing-type find-nested-type
         typedef-properties typedef-events
         rows-with-key interface-impls generic-params method-semantics custom-attributes)

(define (cached rdr key build)
  (define cache (asm-reader-cache rdr))
  (or (hash-ref cache key #f)
      (let ([v (build)]) (hash-set! cache key v) v)))

;; ---------------------------------------------------------------------------------------------
;; Types by name

; A two-level hash, namespace -> name -> rid, so a lookup is two hash-refs on strings and
; allocates nothing. Heap offsets repeat (every type in a namespace shares one), so each string
; is decoded once while building.
(define (name-index rdr table name-col ns-col keep?)
  (define index (make-hash))
  (when (positive? (table-row-count rdr table))
    (define l (table-layout rdr table))
    (define ni (layout-column-index l name-col))
    (define si (layout-column-index l ns-col))
    (define get-string (asm-reader-get-string rdr))
    (define strings (make-hasheqv))
    (define (str offset) (or (hash-ref strings offset #f)
                             (let ([s (get-string offset)]) (hash-set! strings offset s) s)))
    (for ([rid (in-range 1 (add1 (layout-count l)))] #:when (keep? l rid))
      (define names (hash-ref! index (str (layout-raw rdr l rid si)) make-hash))
      ; the first row wins, as in the loader
      (define name (str (layout-raw rdr l rid ni)))
      (unless (hash-ref names name #f) (hash-set! names name rid))))
  index)

; II.22.37 TypeDef: a type is top level when its visibility (flags & 7) is NotPublic (0) or
; Public (1); 2 to 7 are the nested visibilities.
(define (typedef-index rdr)
  (cached rdr 'typedef-index
          (λ () (name-index rdr 'typedef 'name 'namespace
                            (λ (l rid) (< (bitwise-and (layout-raw rdr l rid 0) 7) 2))))))

; The TypeDef rid of a top-level type of any visibility, or #f. ns is "" for no namespace.
(define (find-typedef rdr ns name)
  (define names (hash-ref (typedef-index rdr) ns #f))
  (and names (hash-ref names name #f)))

; II.22.14 ExportedType: top-level rows only, those whose Implementation is not another
; ExportedType (a nested exported type names its enclosing ExportedType there).
(define (find-exported-type rdr ns name)
  (define index
    (cached rdr 'exportedtype-index
            (λ () (name-index rdr 'exportedtype 'type-name 'type-namespace
                              (λ (l rid)
                                (define impl (layout-raw rdr l rid 4))
                                ; II.24.2.6 Implementation tag 2 is ExportedType
                                (not (= (bitwise-and impl 3) 2)))))))
  (define names (hash-ref index ns #f))
  (and names (hash-ref names name #f)))

;; ---------------------------------------------------------------------------------------------
;; Member lists (II.22.37 FieldList and MethodList, II.22.26 ParamList). A row's list runs to the
; next row's list start, or to the end of the target table for the last row.

(define (list-range rdr table rid column target)
  (define l (table-layout rdr table))
  (unless (<= 1 rid (layout-count l)) (error 'list-range "row ~a out of range for ~a" rid table))
  (define i (layout-column-index l column))
  (define start (layout-raw rdr l rid i))
  (define end (if (< rid (layout-count l))
                  (layout-raw rdr l (add1 rid) i)
                  (add1 (table-row-count rdr target))))
  (values start (max start end)))

(define (typedef-methods rdr rid) (list-range rdr 'typedef rid 'method-list 'methoddef))
(define (typedef-fields rdr rid) (list-range rdr 'typedef rid 'field-list 'field))
(define (method-params rdr rid) (list-range rdr 'methoddef rid 'param-list 'param))

; The owner of a member is the last TypeDef whose list starts at or before it. Types with empty
; lists share a start with the next type, so the last such row is the one that owns it.
(define (list-owner rdr column member)
  (define l (table-layout rdr 'typedef))
  (define i (layout-column-index l column))
  (let loop ([lo 1] [hi (layout-count l)] [best #f])
    (if (> lo hi)
        best
        (let ([mid (quotient (+ lo hi) 2)])
          (if (<= (layout-raw rdr l mid i) member)
              (loop (add1 mid) hi mid)
              (loop lo (sub1 mid) best))))))

(define (method-owner rdr method-rid) (list-owner rdr 'method-list method-rid))
(define (field-owner rdr field-rid) (list-owner rdr 'field-list field-rid))

;; ---------------------------------------------------------------------------------------------
;; Rows by key column

; The rids of the rows of table whose key column equals key, in row order. key is a rid for a
; simple index column, or (cons target-table rid) for a coded index column. Sorted tables are
; binary searched on the raw column (II.22: they are sorted by its encoded value); otherwise a
; hash from key to rids is built once and cached.
(define (rows-with-key rdr table column key)
  (cond
    [(zero? (table-row-count rdr table)) '()]
    [else
     (define t (table-by-name table))
     (define l (table-layout rdr table))
     (define i (layout-column-index l column))
     (define raw-key (encode-key t column key))
     (if (and (eq? (table-sorted t) column) (table-sorted? rdr table))
         (sorted-rows rdr l i raw-key)
         (hash-ref (key-index rdr table column l i) raw-key '()))]))

(define (encode-key t column key)
  (cond
    [(exact-nonnegative-integer? key) key]
    [(pair? key)
     (define kind (for/first ([c (in-list (table-columns t))] #:when (eq? (column-name c) column))
                    (column-kind c)))
     (unless (and (pair? kind) (eq? (car kind) 'coded))
       (error 'rows-with-key "~a.~a is not a coded index column" (table-name t) column))
     (coded-encode (cadr kind) (car key) (cdr key))]
    [else (error 'rows-with-key "bad key ~s" key)]))

(define (sorted-rows rdr l i key)
  ; lower bound: the first row whose key is >= key
  (define first
    (let loop ([lo 1] [hi (add1 (layout-count l))])
      (if (< lo hi)
          (let ([mid (quotient (+ lo hi) 2)])
            (if (< (layout-raw rdr l mid i) key) (loop (add1 mid) hi) (loop lo mid)))
          lo)))
  (let loop ([rid first] [acc '()])
    (if (and (<= rid (layout-count l)) (= (layout-raw rdr l rid i) key))
        (loop (add1 rid) (cons rid acc))
        (reverse acc))))

(define (key-index rdr table column l i)
  (cached rdr (string->symbol (format "key-index:~a.~a" table column))
          (λ ()
            (define h (make-hasheqv))
            (for ([rid (in-range (layout-count l) 0 -1)])
              (define k (layout-raw rdr l rid i))
              (hash-set! h k (cons rid (hash-ref h k '()))))
            h)))

;; ---------------------------------------------------------------------------------------------
;; Nesting (II.22.32 NestedClass, sorted by NestedClass)

(define (enclosing-type rdr typedef-rid)
  (define rows (rows-with-key rdr 'nestedclass 'nested-class typedef-rid))
  (and (pair? rows) (row-column-raw rdr 'nestedclass (car rows) 'enclosing-class)))

; The TypeDef rids nested directly in a type, in row order.
(define (nested-types rdr typedef-rid)
  (map (λ (r) (row-column-raw rdr 'nestedclass r 'nested-class))
       (rows-with-key rdr 'nestedclass 'enclosing-class typedef-rid)))

(define (find-nested-type rdr enclosing-rid name)
  (for/first ([rid (in-list (nested-types rdr enclosing-rid))]
              #:when (equal? (row-column rdr 'typedef rid 'name) name))
    rid))

;; ---------------------------------------------------------------------------------------------
;; Properties and events (II.22.35 PropertyMap, II.22.12 EventMap): a type has at most one map
; row, whose list runs to the next map row's list.

(define (map-range rdr map-table list-column target typedef-rid)
  (define rows (rows-with-key rdr map-table 'parent typedef-rid))
  (if (null? rows)
      (values 1 1)
      (list-range rdr map-table (car rows) list-column target)))

(define (typedef-properties rdr rid) (map-range rdr 'propertymap 'property-list 'property rid))
(define (typedef-events rdr rid) (map-range rdr 'eventmap 'event-list 'event rid))

;; ---------------------------------------------------------------------------------------------
;; Common sorted-table lookups

; II.22.23 InterfaceImpl rows of a type
(define (interface-impls rdr typedef-rid) (rows-with-key rdr 'interfaceimpl 'class typedef-rid))

; II.22.20 GenericParam rows of a type or method. owner is (cons 'typedef rid) or
; (cons 'methoddef rid). Rows are sorted by owner, then by number.
(define (generic-params rdr owner) (rows-with-key rdr 'genericparam 'owner owner))

; II.22.28 MethodSemantics rows of a property or event: owner is (cons 'property rid) or
; (cons 'event rid).
(define (method-semantics rdr owner) (rows-with-key rdr 'methodsemantics 'association owner))

; II.22.10 CustomAttribute rows of any HasCustomAttribute parent, e.g. (cons 'typedef rid).
(define (custom-attributes rdr parent) (rows-with-key rdr 'customattribute 'parent parent))
