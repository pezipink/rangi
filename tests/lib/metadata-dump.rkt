#lang racket/base
; Canonical text dump of the metadata tables (ECMA-335 II.22). tests/oracles/srm-dump renders the
; same rows through System.Reflection.Metadata, and the two outputs must match exactly.
; Row decoding lives here rather than in the reader, which only reads table offsets lazily.
(require racket/string file/sha1 "../../src/cli-reader.rkt")
(provide metadata-dump layouts coded-specs column-size le)

; tables dumped, in table-id order
(define dumped-tables '(module typeref typedef methoddef memberref assembly assemblyref methodspec))
; tables read only for their row counts, which bound the lists in typedef and methoddef rows
(define count-only-tables '(field param))

(define table-ids
  (hash 'module #x00 'typeref #x01 'typedef #x02 'field #x04 'methoddef #x06 'param #x08
        'memberref #x0A 'moduleref #x1A 'typespec #x1B 'assembly #x20 'assemblyref #x23))

(define table-titles
  (hash 'module "Module" 'typeref "TypeRef" 'typedef "TypeDef" 'methoddef "MethodDef"
        'memberref "MemberRef" 'assembly "Assembly" 'assemblyref "AssemblyRef"
        'methodspec "MethodSpec"))

; column kinds: (u N) fixed little-endian integer, str and blob and guid heap indexes,
; (simple T) row index into table T, (coded K) coded index (II.24.2.6)
(define layouts
  (hash
   'module '((generation (u 2)) (name str) (mvid guid) (enc-id guid) (enc-base-id guid))
   'typeref '((resolutionscope (coded resolutionscope)) (name str) (namespace str))
   'typedef '((flags (u 4)) (name str) (namespace str) (extends (coded typedeforref))
              (field-list (simple field)) (method-list (simple methoddef)))
   'methoddef '((rva (u 4)) (impl-flags (u 2)) (flags (u 2)) (name str) (signature blob)
                (param-list (simple param)))
   'memberref '((parent (coded memberrefparent)) (name str) (signature blob))
   'assembly '((hash-alg (u 4)) (major (u 2)) (minor (u 2)) (build (u 2)) (revision (u 2))
               (flags (u 4)) (public-key blob) (name str) (culture str))
   'assemblyref '((major (u 2)) (minor (u 2)) (build (u 2)) (revision (u 2)) (flags (u 4))
                  (public-key-or-token blob) (name str) (culture str) (hash-value blob))
   ; II.22.29
   'methodspec '((method (coded methoddeforref)) (instantiation blob))))

; coded index bit width and the tables its tag selects, in tag order
(define coded-specs
  (hash 'typedeforref '(2 typedef typeref typespec)
        'resolutionscope '(2 module moduleref assemblyref typeref)
        'memberrefparent '(3 typedef typeref moduleref methoddef typespec)
        'methoddeforref '(1 methoddef memberref)))

(define (le raw pos size)
  (for/fold ([acc 0]) ([i (in-range size)])
    (+ acc (arithmetic-shift (bytes-ref raw (+ pos i)) (* 8 i)))))

(define (hex8 n)
  (define s (number->string n 16))
  (string-append (make-string (- 8 (string-length s)) #\0) s))

(define (token-text n) (string-append "0x" (hex8 n)))

(define (quoted s) (string-append "\"" s "\""))

(define (column-size rdr kind)
  (cond
    [(eq? kind 'str) (asm-reader-string-index-size rdr)]
    [(eq? kind 'blob) (asm-reader-blob-index-size rdr)]
    [(eq? kind 'guid) (asm-reader-guid-index-size rdr)]
    [(eq? (car kind) 'u) (cadr kind)]
    [(eq? (car kind) 'simple) (table-size rdr (cadr kind))]
    [(eq? (car kind) 'coded) (table-size rdr (cadr kind))]
    [else (error 'metadata-dump "unknown column kind ~s" kind)]))

; simple and coded index sizes come from the reader's encoding table, 2 bytes when absent
(define (table-size rdr name)
  (hash-ref (asm-reader-encoding-sizes rdr) name 2))

; II.23.2 compressed unsigned length, then the blob bytes
(define (blob-at heap idx)
  (define b0 (bytes-ref heap idx))
  (define-values (len start)
    (cond
      [(zero? (bitwise-and b0 #x80)) (values b0 (+ idx 1))]
      [(zero? (bitwise-and b0 #x40))
       (values (bitwise-ior (arithmetic-shift (bitwise-and b0 #x3F) 8) (bytes-ref heap (+ idx 1)))
               (+ idx 2))]
      [else
       (values (bitwise-ior (arithmetic-shift (bitwise-and b0 #x1F) 24)
                            (arithmetic-shift (bytes-ref heap (+ idx 1)) 16)
                            (arithmetic-shift (bytes-ref heap (+ idx 2)) 8)
                            (bytes-ref heap (+ idx 3)))
               (+ idx 4))]))
  (subbytes heap start (+ start len)))

; guid heap is 1-based with 16 bytes per entry; the first three fields are little-endian
(define (guid-text heap idx)
  (cond
    [(zero? idx) (make-string 32 #\0)]
    [else
     (define start (* 16 (- idx 1)))
     (define (reversed from to)
       (list->bytes (reverse (bytes->list (subbytes heap (+ start from) (+ start to))))))
     (string-append (bytes->hex-string (reversed 0 4))
                    (bytes->hex-string (reversed 4 6))
                    (bytes->hex-string (reversed 6 8))
                    (bytes->hex-string (subbytes heap (+ start 8) (+ start 16))))]))

(define (coded-token kind v)
  (define spec (hash-ref coded-specs kind))
  (define bits (car spec))
  (define tags (cdr spec))
  (define tag (bitwise-and v (sub1 (arithmetic-shift 1 bits))))
  (define row (arithmetic-shift v (- bits)))
  (cond
    [(zero? row) 0]
    [(>= tag (length tags)) (error 'metadata-dump "invalid ~a tag ~a" kind tag)]
    [else (bitwise-ior (arithmetic-shift (hash-ref table-ids (list-ref tags tag)) 24) row)]))

(define (read-value rdr kind raw pos)
  (define v (le raw pos (column-size rdr kind)))
  (cond
    [(eq? kind 'str) ((asm-reader-get-string rdr) v)]
    [(eq? kind 'blob) (blob-at (asm-reader-blob-heap rdr) v)]
    [(eq? kind 'guid) (guid-text (asm-reader-guid-heap rdr) v)]
    [(eq? (car kind) 'coded) (coded-token (cadr kind) v)]
    [else v]))

(define (row-count rdr name)
  (define td (hash-ref (asm-reader-table-attributes rdr) name #f))
  (if td (table-data-row-count td) 0))

; decodes every row of a present table; each row is a hash from column name to value
(define (read-rows rdr name)
  (define td (hash-ref (asm-reader-table-attributes rdr) name))
  (define cols (hash-ref layouts name))
  (define raw (asm-reader-raw rdr))
  (define row-size (table-data-row-size td))
  (define total (for/sum ([c cols]) (column-size rdr (cadr c))))
  (unless (= total row-size)
    (error 'metadata-dump "~a rows are ~a bytes but the layout gives ~a" name row-size total))
  (let ([count (table-data-row-count td)])
    (build-vector
     count
     (λ (i)
       (define base (+ (table-data-start-offset td) (* i row-size)))
       (let loop ([cs cols] [pos base] [row (hash)])
         (if (null? cs)
             row
             (let ([c (car cs)])
               (loop (cdr cs)
                     (+ pos (column-size rdr (cadr c)))
                     (hash-set row (car c) (read-value rdr (cadr c) raw pos))))))))))

; II.22.37: a row's list runs from its start up to the next row's start, or to the end of the target table
(define (list-text rows i key target-count)
  (define start (hash-ref (vector-ref rows i) key))
  (define end (if (< (+ i 1) (vector-length rows))
                  (- (hash-ref (vector-ref rows (+ i 1)) key) 1)
                  target-count))
  (if (< end start) "[]" (format "[~a..~a]" start end)))

(define (version-text row)
  (format "~a.~a.~a.~a" (hash-ref row 'major) (hash-ref row 'minor)
          (hash-ref row 'build) (hash-ref row 'revision)))

; II.25.4 tiny (flags 2) and fat (flags 3) method headers
(define (il-code rdr rva)
  (define raw (asm-reader-raw rdr))
  (define pos ((asm-reader-resolve-rva rdr) rva))
  (define b0 (bytes-ref raw pos))
  (cond
    [(= (bitwise-and b0 3) 2)
     (subbytes raw (+ pos 1) (+ pos 1 (arithmetic-shift b0 -2)))]
    [(= (bitwise-and b0 3) 3)
     (let ([header-size (* 4 (arithmetic-shift (le raw pos 2) -12))]
           [code-size (le raw (+ pos 4) 4)])
       (subbytes raw (+ pos header-size) (+ pos header-size code-size)))]
    [else (error 'metadata-dump "unknown method header at rva ~a" rva)]))

(define (row-fields rdr name rows i)
  (define row (vector-ref rows i))
  (define (ref key) (hash-ref row key))
  (case name
    [(module)
     (list (string-append "Name=" (quoted (ref 'name)))
           (string-append "Mvid=" (ref 'mvid)))]
    [(typeref)
     (list (string-append "ResolutionScope=" (token-text (ref 'resolutionscope)))
           (string-append "Name=" (quoted (ref 'name)))
           (string-append "Namespace=" (quoted (ref 'namespace))))]
    [(typedef)
     (list (format "Flags=~a" (ref 'flags))
           (string-append "Name=" (quoted (ref 'name)))
           (string-append "Namespace=" (quoted (ref 'namespace)))
           (string-append "Extends=" (token-text (ref 'extends)))
           (string-append "Fields=" (list-text rows i 'field-list (row-count rdr 'field)))
           (string-append "Methods=" (list-text rows i 'method-list (row-count rdr 'methoddef))))]
    [(methoddef)
     (append
      (list (format "Rva=~a" (ref 'rva))
            (format "ImplFlags=~a" (ref 'impl-flags))
            (format "Flags=~a" (ref 'flags))
            (string-append "Name=" (quoted (ref 'name)))
            (string-append "Signature=" (bytes->hex-string (ref 'signature)))
            (string-append "Params=" (list-text rows i 'param-list (row-count rdr 'param))))
      (if (zero? (ref 'rva))
          '()
          (list (string-append "Il=" (bytes->hex-string (il-code rdr (ref 'rva)))))))]
    [(memberref)
     (list (string-append "Parent=" (token-text (ref 'parent)))
           (string-append "Name=" (quoted (ref 'name)))
           (string-append "Signature=" (bytes->hex-string (ref 'signature))))]
    [(assembly)
     (list (format "HashAlgorithm=~a" (ref 'hash-alg))
           (string-append "Version=" (version-text row))
           (format "Flags=~a" (ref 'flags))
           (string-append "PublicKey=" (bytes->hex-string (ref 'public-key)))
           (string-append "Name=" (quoted (ref 'name)))
           (string-append "Culture=" (quoted (ref 'culture))))]
    [(methodspec)
     (list (string-append "Method=" (token-text (ref 'method)))
           (string-append "Instantiation=" (bytes->hex-string (ref 'instantiation))))]
    [(assemblyref)
     (list (string-append "Version=" (version-text row))
           (format "Flags=~a" (ref 'flags))
           (string-append "PublicKeyOrToken=" (bytes->hex-string (ref 'public-key-or-token)))
           (string-append "Name=" (quoted (ref 'name)))
           (string-append "Culture=" (quoted (ref 'culture)))
           (string-append "HashValue=" (bytes->hex-string (ref 'hash-value))))]))

(define (render-table rdr name)
  (define rows (read-rows rdr name))
  (define title (hash-ref table-titles name))
  (cons (format "~a rows=~a" title (vector-length rows))
        (for/list ([i (in-range (vector-length rows))])
          (format "  ~a[~a] ~a" title (+ i 1) (string-join (row-fields rdr name rows i) " ")))))

(define (check-supported rdr)
  (for ([(name td) (in-hash (asm-reader-table-attributes rdr))])
    (when (and (> (table-data-row-count td) 0)
               (not (memq name dumped-tables))
               (not (memq name count-only-tables)))
      (error 'metadata-dump "table ~a is not supported" name))))

; returns the dump with LF line endings and a trailing newline
(define (metadata-dump rdr)
  (check-supported rdr)
  (apply string-append
         (for*/list ([name dumped-tables]
                     #:when (> (row-count rdr name) 0)
                     [line (render-table rdr name)])
           (string-append line "\n"))))
