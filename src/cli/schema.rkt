#lang racket/base
; The single source of truth for CLI metadata table layouts (ECMA-335 II.22) and
; coded index kinds (II.24.2.6). The reader and the writer derive row sizes, index
; widths and coded index encodings from the data here.
;
; Column kinds:
;   u8 u16 u32    fixed-width integers
;   string        index into #Strings
;   guid          index into #GUID (1-based, 0 is null)
;   blob          index into #Blob
;   (index t)     simple index into table t
;   (coded k)     coded index of kind k
;
; Everything is kept in lists and vectors, so the order never depends on hashing.

(provide (struct-out table)
         (struct-out column)
         (struct-out coded-kind)
         schema-tables
         schema-coded-kinds
         table-by-id
         table-by-name
         coded-kind-by-name
         simple-index-width
         coded-index-width
         column-width
         row-size
         coded-encode
         coded-decode)

; sorted is the name of the column the rows are sorted by, or #f (II.22, sorted bit vector)
(struct table (id name sorted columns))
(struct column (name kind))
; targets is a vector indexed by tag. #f marks a tag that is not used.
(struct coded-kind (name bits targets))

(define (def id name sorted . cols)
  (table id name sorted
         (for/list ([c (in-list cols)])
           (column (car c) (cadr c)))))

(define (coded name bits . targets)
  (coded-kind name bits (list->vector targets)))

(define schema-tables
  (list
   (def #x00 'module #f
     '(generation u16) '(name string) '(mvid guid) '(enc-id guid) '(enc-base-id guid))
   (def #x01 'typeref #f
     '(resolution-scope (coded resolutionscope)) '(name string) '(namespace string))
   (def #x02 'typedef #f
     '(flags u32) '(name string) '(namespace string) '(extends (coded typedeforref))
     '(field-list (index field)) '(method-list (index methoddef)))
   (def #x03 'fieldptr #f
     '(field (index field)))
   (def #x04 'field #f
     '(flags u16) '(name string) '(signature blob))
   (def #x05 'methodptr #f
     '(method (index methoddef)))
   (def #x06 'methoddef #f
     '(rva u32) '(impl-flags u16) '(flags u16) '(name string) '(signature blob)
     '(param-list (index param)))
   (def #x07 'paramptr #f
     '(param (index param)))
   (def #x08 'param #f
     '(flags u16) '(sequence u16) '(name string))
   (def #x09 'interfaceimpl 'class
     '(class (index typedef)) '(interface (coded typedeforref)))
   (def #x0A 'memberref #f
     '(class (coded memberrefparent)) '(name string) '(signature blob))
   (def #x0B 'constant 'parent
     '(type u8) '(padding u8) '(parent (coded hasconstant)) '(value blob))
   (def #x0C 'customattribute 'parent
     '(parent (coded hascustomattribute)) '(type (coded customattributetype)) '(value blob))
   (def #x0D 'fieldmarshal 'parent
     '(parent (coded hasfieldmarshal)) '(native-type blob))
   (def #x0E 'declsecurity 'parent
     '(action u16) '(parent (coded hasdeclsecurity)) '(permission-set blob))
   (def #x0F 'classlayout 'parent
     '(packing-size u16) '(class-size u32) '(parent (index typedef)))
   (def #x10 'fieldlayout 'field
     '(offset u32) '(field (index field)))
   (def #x11 'standalonesig #f
     '(signature blob))
   (def #x12 'eventmap #f
     '(parent (index typedef)) '(event-list (index event)))
   (def #x13 'eventptr #f
     '(event (index event)))
   (def #x14 'event #f
     '(event-flags u16) '(name string) '(event-type (coded typedeforref)))
   (def #x15 'propertymap #f
     '(parent (index typedef)) '(property-list (index property)))
   (def #x16 'propertyptr #f
     '(property (index property)))
   (def #x17 'property #f
     '(flags u16) '(name string) '(type blob))
   (def #x18 'methodsemantics 'association
     '(semantics u16) '(method (index methoddef)) '(association (coded hassemantics)))
   (def #x19 'methodimpl 'class
     '(class (index typedef)) '(method-body (coded methoddeforref))
     '(method-declaration (coded methoddeforref)))
   (def #x1A 'moduleref #f
     '(name string))
   (def #x1B 'typespec #f
     '(signature blob))
   (def #x1C 'implmap 'member-forwarded
     '(mapping-flags u16) '(member-forwarded (coded memberforwarded))
     '(import-name string) '(import-scope (index moduleref)))
   (def #x1D 'fieldrva 'field
     '(rva u32) '(field (index field)))
   (def #x1E 'enclog #f
     '(token u32) '(func-code u32))
   (def #x1F 'encmap #f
     '(token u32))
   (def #x20 'assembly #f
     '(hash-alg-id u32) '(major-version u16) '(minor-version u16) '(build-number u16)
     '(revision-number u16) '(flags u32) '(public-key blob) '(name string) '(culture string))
   (def #x21 'assemblyprocessor #f
     '(processor u32))
   (def #x22 'assemblyos #f
     '(os-platform-id u32) '(os-major-version u32) '(os-minor-version u32))
   (def #x23 'assemblyref #f
     '(major-version u16) '(minor-version u16) '(build-number u16) '(revision-number u16)
     '(flags u32) '(public-key-or-token blob) '(name string) '(culture string)
     '(hash-value blob))
   (def #x24 'assemblyrefprocessor #f
     '(processor u32) '(assemblyref (index assemblyref)))
   (def #x25 'assemblyrefos #f
     '(os-platform-id u32) '(os-major-version u32) '(os-minor-version u32)
     '(assemblyref (index assemblyref)))
   (def #x26 'file #f
     '(flags u32) '(name string) '(hash-value blob))
   (def #x27 'exportedtype #f
     '(flags u32) '(type-def-id u32) '(type-name string) '(type-namespace string)
     '(implementation (coded implementation)))
   (def #x28 'manifestresource #f
     '(offset u32) '(flags u32) '(name string) '(implementation (coded implementation)))
   (def #x29 'nestedclass 'nested-class
     '(nested-class (index typedef)) '(enclosing-class (index typedef)))
   (def #x2A 'genericparam 'owner
     '(number u16) '(flags u16) '(owner (coded typeormethoddef)) '(name string))
   (def #x2B 'methodspec #f
     '(method (coded methoddeforref)) '(instantiation blob))
   (def #x2C 'genericparamconstraint 'owner
     '(owner (index genericparam)) '(constraint (coded typedeforref)))))

; II.24.2.6. Unused tags are #f. The tag occupies the low `bits` bits of the value.
(define schema-coded-kinds
  (list
   (coded 'typedeforref 2 'typedef 'typeref 'typespec)
   (coded 'hasconstant 2 'field 'param 'property)
   (coded 'hascustomattribute 5
          'methoddef 'field 'typeref 'typedef 'param 'interfaceimpl 'memberref 'module
          'declsecurity 'property 'event 'standalonesig 'moduleref 'typespec 'assembly
          'assemblyref 'file 'exportedtype 'manifestresource 'genericparam
          'genericparamconstraint 'methodspec)
   (coded 'hasfieldmarshal 1 'field 'param)
   (coded 'hasdeclsecurity 2 'typedef 'methoddef 'assembly)
   (coded 'memberrefparent 3 'typedef 'typeref 'moduleref 'methoddef 'typespec)
   (coded 'hassemantics 1 'event 'property)
   (coded 'methoddeforref 1 'methoddef 'memberref)
   (coded 'memberforwarded 1 'field 'methoddef)
   (coded 'implementation 2 'file 'assemblyref 'exportedtype)
   (coded 'customattributetype 3 #f #f 'methoddef 'memberref #f)
   (coded 'resolutionscope 2 'module 'moduleref 'assemblyref 'typeref)
   (coded 'typeormethoddef 1 'typedef 'methoddef)))

(define (table-by-id id)
  (for/first ([t (in-list schema-tables)] #:when (= (table-id t) id)) t))

(define (table-by-name name)
  (for/first ([t (in-list schema-tables)] #:when (eq? (table-name t) name)) t))

(define (coded-kind-by-name name)
  (or (for/first ([k (in-list schema-coded-kinds)] #:when (eq? (coded-kind-name k) name)) k)
      (error 'schema "unknown coded index kind ~a" name)))

; every table and coded kind named by a column must exist, or the widths would
; silently come out as zero rows
(let ([names (map table-name schema-tables)])
  (define (check-table name)
    (unless (memq name names) (error 'schema "unknown table ~a" name)))
  (for* ([t (in-list schema-tables)] [c (in-list (table-columns t))])
    (define kind (column-kind c))
    (cond
      [(not (pair? kind)) (void)]
      [(eq? (car kind) 'index) (check-table (cadr kind))]
      [else (coded-kind-by-name (cadr kind))]))
  (for* ([k (in-list schema-coded-kinds)] [t (in-vector (coded-kind-targets k))] #:when t)
    (check-table t)))

; a simple index is 4 bytes only when some row number does not fit in 16 bits (II.24.2.6)
(define (simple-index-width rows)
  (if (> rows #xFFFF) 4 2))

; a coded index is 4 bytes when the largest target row count does not fit in the
; 16 - bits bits left after the tag (II.24.2.6). Absent tables have zero rows.
(define (coded-index-width k rows-of)
  (define largest
    (for/fold ([m 0]) ([t (in-vector (coded-kind-targets k))] #:when t)
      (max m (rows-of t))))
  (if (< largest (expt 2 (- 16 (coded-kind-bits k)))) 2 4))

; rows-of maps a table name to its row count (0 when the table is absent)
(define (column-width kind string-size blob-size guid-size rows-of)
  (cond
    [(symbol? kind)
     (case kind
       [(u8) 1]
       [(u16) 2]
       [(u32) 4]
       [(string) string-size]
       [(guid) guid-size]
       [(blob) blob-size]
       [else (error 'schema "unknown column kind ~a" kind)])]
    [(eq? (car kind) 'index) (simple-index-width (rows-of (cadr kind)))]
    [else (coded-index-width (coded-kind-by-name (cadr kind)) rows-of)]))

(define (row-size t string-size blob-size guid-size rows-of)
  (for/sum ([c (in-list (table-columns t))])
    (column-width (column-kind c) string-size blob-size guid-size rows-of)))

(define (coded-encode name target rid)
  (define k (coded-kind-by-name name))
  (define tag
    (for/first ([t (in-vector (coded-kind-targets k))] [i (in-naturals)] #:when (eq? t target)) i))
  (unless tag (error 'coded-encode "~a is not a target of ~a" target name))
  (bitwise-ior (arithmetic-shift rid (coded-kind-bits k)) tag))

; returns the target table name (#f for an unused tag) and the row number
(define (coded-decode k value)
  (define bits (coded-kind-bits k))
  (define tag (bitwise-and value (- (arithmetic-shift 1 bits) 1)))
  (values (vector-ref (coded-kind-targets k) tag)
          (arithmetic-shift value (- bits))))
