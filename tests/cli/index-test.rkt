#lang racket/base
; Reader indexes (src/cli/index.rkt) checked against mscorlib: known facts about well-known
; types, every sorted-table lookup cross-checked against a linear scan, the hash fallback used
; when the Sorted mask is clear, and caching on the reader. Skipped when mscorlib is missing.
(require rackunit racket/list
         "../../src/cli/reader.rkt" "../../src/cli/index.rkt" "../oracles/tools.rkt")

(define mscorlib
  (let ([dir (find-directory "RANGI_REFERENCE_ASSEMBLIES" net471-reference-dir)])
    (and dir
         (let ([p (build-path dir "mscorlib.dll")])
           (and (file-exists? p) (path->string p))))))

(define (names rdr table rids)
  (for/list ([rid rids]) (row-column rdr table rid 'name)))

; rows of table whose decoded column equals key, by brute force
(define (scan rdr table column key)
  (for/list ([rid (in-range 1 (add1 (table-row-count rdr table)))]
             #:when (equal? (row-column rdr table rid column) key))
    rid))

(define (run-tests rdr)
  (define string-rid (find-typedef rdr "System" "String"))

  (test-case "find-typedef finds top-level types and only those"
    (check-true (exact-positive-integer? string-rid))
    (check-equal? (row-column rdr 'typedef string-rid 'name) "String")
    (check-equal? (row-column rdr 'typedef string-rid 'namespace) "System")
    (check-false (find-typedef rdr "System" "NoSuchType"))
    (check-false (find-typedef rdr "NoSuch.Namespace" "String"))
    ; nested types have an empty namespace but are not top level
    (check-false (find-typedef rdr "" "SpecialFolder"))
    (check-true (exact-positive-integer? (find-typedef rdr "System.Collections.Generic" "List`1"))))

  (test-case "find-typedef agrees with a scan of every top-level TypeDef"
    (for ([rid (in-range 1 (add1 (table-row-count rdr 'typedef)))]
          #:when (< (bitwise-and (row-column rdr 'typedef rid 'flags) 7) 2))
      (define found (find-typedef rdr (row-column rdr 'typedef rid 'namespace)
                                  (row-column rdr 'typedef rid 'name)))
      ; duplicates keep the first row
      (check-true (and found (<= found rid)))))

  (test-case "method and field ranges, and their owners"
    (define methods-of-string (typedef-methods rdr string-rid))
    (define methods (names rdr 'methoddef methods-of-string))
    (check-not-false (member "Concat" methods))
    (check-not-false (member "get_Length" methods))
    (for ([m methods-of-string]) (check-equal? (method-owner rdr m) string-rid))
    (define fields-of-string (typedef-fields rdr string-rid))
    (check-not-false (member "Empty" (names rdr 'field fields-of-string)))
    (for ([f fields-of-string]) (check-equal? (field-owner rdr f) string-rid))
    ; every method's owner lists it
    (for ([m (in-range 1 (add1 (table-row-count rdr 'methoddef)) 97)])
      (check-not-false (memv m (for/list ([x (typedef-methods rdr (method-owner rdr m))]) x)))))

  (test-case "method params"
    (define compare
      (for/first ([m (typedef-methods rdr string-rid)]
                  #:when (and (equal? (row-column rdr 'methoddef m 'name) "Compare")
                              (= (length (for/list ([p (method-params rdr m)]) p)) 2)))
        m))
    (check-equal? (names rdr 'param (method-params rdr compare)) '("strA" "strB")))

  (test-case "nested types"
    (define env (find-typedef rdr "System" "Environment"))
    (define folder (find-nested-type rdr env "SpecialFolder"))
    (check-true (exact-positive-integer? folder))
    (check-equal? (enclosing-type rdr folder) env)
    (check-not-false (member folder (nested-types rdr env)))
    (check-false (enclosing-type rdr string-rid))
    (check-false (find-nested-type rdr env "NoSuchType")))

  (test-case "interfaces, generic params, properties and their accessors"
    (define interfaces
      (for/list ([r (in-list (interface-impls rdr string-rid))])
        (define i (row-column rdr 'interfaceimpl r 'interface))
        (and (eq? (car i) 'typedef) (row-column rdr 'typedef (cdr i) 'name))))
    (check-not-false (member "IComparable" interfaces))
    (define list-rid (find-typedef rdr "System.Collections.Generic" "List`1"))
    (check-equal? (for/list ([r (generic-params rdr (cons 'typedef list-rid))])
                    (row-column rdr 'genericparam r 'name))
                  '("T"))
    (define length-prop
      (for/first ([p (typedef-properties rdr string-rid)] #:when (equal? (row-column rdr 'property p 'name) "Length"))
        p))
    (check-true (exact-positive-integer? length-prop))
    (check-equal? (for/list ([r (method-semantics rdr (cons 'property length-prop))])
                    (row-column rdr 'methoddef (row-column rdr 'methodsemantics r 'method) 'name))
                  '("get_Length"))
    (check-not-false (member "UnhandledException"
                             (names rdr 'event (typedef-events rdr (find-typedef rdr "System" "AppDomain"))))))

  (test-case "sorted-table lookups agree with a linear scan"
    (for ([spec (in-list '((interfaceimpl class) (genericparam owner) (nestedclass nested-class)
                           (nestedclass enclosing-class) (methodsemantics association)
                           (customattribute parent) (constant parent) (propertymap parent)))])
      (define table (first spec))
      (define column (second spec))
      (define n (table-row-count rdr table))
      ; every 37th row's key, plus keys that match nothing
      (define keys (append (for/list ([rid (in-range 1 (add1 n) 37)])
                             (row-column rdr table rid column))
                           (list (if (pair? (row-column rdr table 1 column))
                                     (cons (car (row-column rdr table 1 column)) 999999)
                                     999999))))
      (for ([key (in-list keys)])
        (check-equal? (rows-with-key rdr table column key) (scan rdr table column key)
                      (format "~a.~a = ~s" table column key))))))

(cond
  [mscorlib
   (define rdr (read-file mscorlib))
   (test-case "mscorlib marks its sorted tables sorted"
     (check-true (table-sorted? rdr 'interfaceimpl))
     (check-true (table-sorted? rdr 'customattribute))
     (check-false (table-sorted? rdr 'typedef)))
   (run-tests rdr)

   (test-case "the same answers come from the hash fallback when nothing is marked sorted"
     (define unsorted (read-file mscorlib))
     (set-asm-reader-sorted-mask! unsorted 0)
     (run-tests unsorted)
     (check-true (for/or ([k (in-hash-keys (asm-reader-cache unsorted))])
                   (regexp-match? #rx"^key-index:" (symbol->string k)))))

   (test-case "indexes are cached on the reader, and each read-file starts empty"
     (check-eq? (hash-ref (asm-reader-cache rdr) 'typedef-index)
                (begin (find-typedef rdr "System" "Object")
                       (hash-ref (asm-reader-cache rdr) 'typedef-index)))
     (check-false (hash-ref (asm-reader-cache (read-file mscorlib)) 'typedef-index #f)))]
  [else (printf "skipping index-test: mscorlib.dll not found\n")])
