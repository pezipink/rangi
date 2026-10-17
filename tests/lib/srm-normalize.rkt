#lang racket/base
; Normalises a System.Reflection.Metadata dump (tests/oracles/srm-dump) so that two images built
; from the same source compare equal when their layout differs. Row indexes, row order, RVAs,
; method bodies, MVIDs, assembly identity, and optional Param rows are dropped. Tokens and class
; references in signatures become names, so a reordered TypeDef table still compares equal.
(require racket/list racket/string racket/format)
(provide normalize-srm-dump)

; II.22.33 Param rows are optional, so ilasm's named Param rows are not compared.
; Assembly identity (II.22.2, II.22.5) differs by design, and the module is named by its .module.
(define dropped-tables '("Assembly" "AssemblyRef" "Param"))
(define dropped-keys '("Mvid" "Rva" "Il" "Params"))

(define header-rx #px"^([A-Za-z]+) rows=([0-9]+)$")
(define row-rx #px"^  ([A-Za-z]+)\\[([0-9]+)\\] ?(.*)$")
(define pair-rx #px"([A-Za-z]+)=(\"[^\"]*\"|\\[[^\\]]*\\]|\\S*)")
(define range-rx #px"^\\[([0-9]+)\\.\\.([0-9]+)\\]$")

; returns the table headers in dump order, and a hash from table name to a hash from row index
; to an alist of (key . value), with quotes removed from values
(define (parse-dump text)
  (define tables (make-hash))
  (define lines (for/list ([line (in-list (string-split text "\n"))])
                  (string-trim line "\r" #:left? #f)))
  (define headers
    (for*/list ([line (in-list lines)]
                [m (in-value (regexp-match header-rx line))]
                #:when m)
      (cons (cadr m) (string->number (caddr m)))))
  (for ([line (in-list lines)])
    (define m (regexp-match row-rx line))
    (when m
      (define rows (hash-ref! tables (cadr m) make-hash))
      (define pairs
        (for/list ([kv (in-list (regexp-match* pair-rx (cadddr m) #:match-select cdr))])
          (cons (car kv) (unquote-value (cadr kv)))))
      (hash-set! rows (string->number (caddr m)) pairs)))
  (values headers tables))

(define (unquote-value v)
  (if (and (>= (string-length v) 2) (char=? (string-ref v 0) #\"))
      (substring v 1 (sub1 (string-length v)))
      v))

(define (row-of tables table idx)
  (hash-ref (hash-ref tables table (hash)) idx #f))

(define (field-of pairs key)
  (let ([p (assoc key pairs)]) (and p (cdr p))))

(define (qualified ns name)
  (if (string=? ns "") name (string-append ns "." name)))

; a token is a table id in the top byte and a 1-based row index in the low 24 bits (II.3.1)
(define (token-name tables tok)
  (define v (string->number (substring tok 2) 16))
  (define tag (arithmetic-shift v -24))
  (define idx (bitwise-and v #xFFFFFF))
  (define (named table)
    (define row (row-of tables table idx))
    (cond [row (field-of row "Name")]
          [else (format "?~a:~a" table idx)]))
  (cond
    [(zero? idx) "null"]
    [(= tag #x01)
     (define row (row-of tables "TypeRef" idx))
     (define scope (field-of row "ResolutionScope"))
     (string-append (scope-prefix tables scope)
                    (qualified (field-of row "Namespace") (field-of row "Name")))]
    [(= tag #x02)
     (define row (row-of tables "TypeDef" idx))
     (qualified (field-of row "Namespace") (field-of row "Name"))]
    [(= tag #x04) (named "Field")]
    [(= tag #x06) (named "MethodDef")]
    [(= tag #x08)
     (define row (row-of tables "Param" idx))
     (if row
         (format "Param:~a:~a" (field-of row "Sequence") (field-of row "Name"))
         tok)]
    [(= tag #x0A) (named "MemberRef")]
    [(= tag #x23) (format "[~a]" (named "AssemblyRef"))]
    [else tok]))

(define (scope-prefix tables scope)
  (if (and scope (regexp-match? #rx"^0x23" scope))
      (string-append "[" (token-name tables scope) "]")
      ""))

; a signature is a byte sequence (II.23.2). Element types 0x11 (VALUETYPE) and 0x12 (CLASS) are
; followed by a TypeDefOrRefOrSpecEncoded index, which is a compressed uint whose low two bits
; select the table. Any other byte is kept as hex. This walk is a heuristic: it assumes that no
; literal count or argument byte equals 0x11 or 0x12, which holds for the fixtures compared.
(define (normalize-signature tables hex)
  (define bs (for/list ([i (in-range 0 (string-length hex) 2)])
               (string->number (substring hex i (+ i 2)) 16)))
  (let loop ([bs bs] [acc '()])
    (cond
      [(null? bs) (string-join (reverse acc) " ")]
      [(and (memv (car bs) '(#x11 #x12)) (pair? (cdr bs)))
       (define-values (value rest) (read-compressed (cdr bs)))
       (define tag (bitwise-and value 3))
       (define idx (arithmetic-shift value -2))
       (define name
         (case tag
           [(0) (token-name tables (format "0x02~a" (~r idx #:base 16 #:min-width 6 #:pad-string "0")))]
           [(1) (token-name tables (format "0x01~a" (~r idx #:base 16 #:min-width 6 #:pad-string "0")))]
           [else "typespec"]))
       (loop rest (cons (format "~a:~a" (if (= (car bs) #x11) "valuetype" "class") name) acc))]
      [else (loop (cdr bs) (cons (~r (car bs) #:base 16 #:min-width 2 #:pad-string "0") acc))])))

; compressed unsigned integer (II.23.2)
(define (read-compressed bs)
  (define b (car bs))
  (cond
    [(zero? (bitwise-and b #x80)) (values b (cdr bs))]
    [(zero? (bitwise-and b #xC0))
     (values (bitwise-ior (arithmetic-shift (bitwise-and b #x3F) 8) (cadr bs)) (cddr bs))]
    [else
     (values (bitwise-ior (arithmetic-shift (bitwise-and b #x1F) 24)
                          (arithmetic-shift (cadr bs) 16)
                          (arithmetic-shift (caddr bs) 8)
                          (cadddr bs))
             (cddddr bs))]))

(define (normalize-range tables target value)
  (define m (regexp-match range-rx value))
  (cond
    [m
     (define a (string->number (cadr m)))
     (define b (string->number (caddr m)))
     (string-append
      "["
      (string-join
       (for/list ([i (in-range a (add1 b))])
         (let ([row (row-of tables target i)])
           (if row (field-of row "Name") "?")))
       ",")
      "]")]
    [else "[]"]))

; ClassLayout.Parent and FieldLayout.Field are plain row numbers, not tokens (II.22.8, II.22.16),
; so they are named through their rows.
(define (plain-row-name tables target value key)
  (define idx (string->number value))
  (define row (and idx (row-of tables target idx)))
  (cond
    [(not row) value]
    [(equal? target "TypeDef") (qualified (field-of row "Namespace") (field-of row key))]
    [else (field-of row key)]))

(define (normalize-value tables table key value)
  (cond
    [(and (equal? table "ClassLayout") (equal? key "Parent"))
     (plain-row-name tables "TypeDef" value "Name")]
    [(and (equal? table "FieldLayout") (equal? key "Field"))
     (plain-row-name tables "Field" value "Name")]
    [(member key '("Extends" "ResolutionScope" "Parent"))
     (token-name tables value)]
    [(equal? key "Fields") (normalize-range tables "Field" value)]
    [(equal? key "Methods") (normalize-range tables "MethodDef" value)]
    [(equal? key "Signature") (normalize-signature tables value)]
    [else value]))

(define (normalize-row tables table pairs)
  (string-join
   (for/list ([kv (in-list pairs)]
              #:unless (member (car kv) dropped-keys))
     (string-append (car kv) "=" (normalize-value tables table (car kv) (cdr kv))))
   " "))

; returns the normalised dump as a string, with the rows of each table sorted
(define (normalize-srm-dump text)
  (define-values (headers tables) (parse-dump text))
  (string-join
   (append*
    (for/list ([h (in-list headers)]
               #:unless (member (car h) dropped-tables))
      (define table (car h))
      (define rows (hash-ref tables table (hash)))
      (define lines
        (sort (for/list ([(idx pairs) (in-hash rows)])
                (string-append "  " (normalize-row tables table pairs)))
              string<?))
      (cons (format "~a rows=~a" table (cdr h)) lines)))
   "\n"))
