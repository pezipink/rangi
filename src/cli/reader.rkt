#lang racket/base
(require racket/string)
(require "../pe/read.rkt")
(require "../private/binary.rkt")
(require "schema.rkt")
(require "sigs.rkt")
; read-only accessors for tests that decode table rows. row decoding stays out of the reader,
; so the lazy path used by the macro expander is unchanged.
(provide read-file get-public-typedefs read-assembly-meta read-row read-metadata-root
         row-column row-column-raw table-row-count table-sorted?
         table-layout layout-count layout-column-index layout-raw
         asm-reader-cache asm-reader-sorted-mask set-asm-reader-sorted-mask!
         (struct-out method-signature)
         decode-typespec decode-method-sig decode-localvar-sig decode-method-instantiation
         asm-reader-raw asm-reader-string-index-size asm-reader-blob-index-size
         asm-reader-guid-index-size asm-reader-encoding-sizes asm-reader-table-attributes
         asm-reader-get-string asm-reader-resolve-rva asm-reader-string-heap asm-reader-blob-heap
         asm-reader-guid-heap
         table-data-row-count table-data-row-size table-data-start-offset)
(define (int->hex n)
  (number->string n 16)) 

(define (bits-set? mask int)
  (equal? (bitwise-and mask int) mask))

(define (bits-not-set? mask int)
  (equal? (bitwise-and mask int) 0))

(struct table-data
  ([type]
   [row-count]
   [ordinal]
   [row-size #:auto]
   [start-offset #:auto])
  #:mutable
  #:transparent)
        
; when reading the files we want to be as lazy as we can.
; the references will be loaded at expansion time so it must
; be as fast as possible, only loading the minium required.
; this struct provides everything needed for fast access to
; any metadata table and row after inital load.
(struct asm-reader  
  (   
   [filename #:auto]
   ; raw bytestring of whole file
   [raw #:auto]
   ; entire string heap byte string
   [string-heap #:auto]
   ; entire user string heap byte string
   [us-heap #:auto]
   ; entire blob heap byte string
   [blob-heap #:auto]
   ; entire guid heap byte string
   [guid-heap #:auto]
   ; offset where the cli metadata starts
   [metadata-root #:auto]

   ; calculated index sizes in bytes
   [string-index-size #:auto]
   [blob-index-size #:auto]
   [guid-index-size #:auto]
      
   ; list of present tables, in order
   [present-tables #:auto]

   ; hash that returns the amount of bytes taken
   ; for an encoding type; this can be a table name,
   ; or a compound coded index type:
   ; 'typedeforref 'hasconstant
   ; 'hascustomattribute 'hasfieldmarshal
   ; 'hasdeclsecurity 'memberrefparent 'hassemantics
   ; 'methoddeforref 'memberforwarded 'implementation
   ; 'customattributetype 'resolutionscope
   ; 'typeormethoddef
   [encoding-sizes #:auto]
   
   ; hash of table-data, keyed by type
   [table-attributes #:auto]
   
   ; function accepting offset and returning string from String heap
   [get-string #:auto]

   ; function that resolves an rva
   [resolve-rva #:auto]

   ; II.24.2.6 Sorted: bit n is set when table n is sorted by its key column
   [sorted-mask #:auto]

   ; hasheq of everything derived from the bytes on first use: column layouts and the scanned
   ; indexes in index.rkt. Its lifetime is this reader's; read-file always starts a fresh one.
   [cache #:auto]
   
  ) 
  #:mutable
  #:transparent)


#;(define (asm-reader->string offset reader)
  (define heap (asm-reader-string-heap))
  (define (aux start offset)
    (cond       
      [(equal? (bytes-ref heap (+ start offset)) 0)
       ; end of string
       (bytes->string/latin-1 (subbytes heap start (+ start offset 1)))]       
      [else (aux start (+ offset 1))])) 
  (aux offset 0))
  
  

(define import-table-spec
  '(
    (lookup-rva 4)
   (stamp 4)
   (fwd-chain 4)
   (name-rva 4)
   (address-rva 4) ; this should be the same rva asin the header
   (blank 8) ;padding
   (blank2 8) ;padding
   (blank3 4) ;padding
    ))

(define import-lookup-table-spec
  '(
    (hint-name-rva 4)
    ;in a normal pe there'd be a 4 byte rva for each imported symbol,
    ; but here we have only 1
   (blank3 4) ;padding
    ))

(define iat-table-spec
  '(
    (hint 2) ; blank
    ;in a normal pe there'd be a 4 byte rva for each imported symbol,
    ; but here we have only 1
    ; the null-terminated strings follow
    ))

(define cli-header-spec
  '(
    (size 4)
    (major 2)
    (minor 2)
    (metadata-rva 4)
    (metadata-size 4)
    (flags 4)
    (entry-token 4)
    (res-rva 4)
    (res-size 4)
    (strong-sig 8)
    (codeman 8)
    (vtable-fix 8)
    (export-jumps 8)
    (managed-header 8)
    ))

(define cli-meta-root-spec
  '((magic 4)))

(define (parse-cli-stream-header port)
  ; offset to start of stream from metadata root
  (define offset (read-u32-le port))
  (define size (read-u32-le port))
  (define name-start (file-position port))
  ;the name does not have its size specified, we must
  ;read a null-terminated string. max 32.
  (define name-raw (make-bytes 32))
  (define (aux i)
    (let ([next (read-byte port)])
      (bytes-set! name-raw i next)
      (when (not (equal? next 0))
        (aux (+ i 1)))))
  
  (aux 0)
  ;chop off blanks
  (define name (subbytes name-raw 0 (- (file-position port) name-start 1)))
  
  ;read blank chars to 4 byte align. 
  (when (> (modulo (file-position port) 4) 0)
    (read-bytes (- 4 (modulo (file-position port) 4)) port))
  
  (make-hash `((offset ,@offset) (size ,@size) (name ,@name))))

;todo: maybe use this spec approach for both size calc and parsing rows
#;(define (gen-table-specs string-size blob-size guid-size coded-index-sizes)
  ; shorthands
  (define ss string-size)
  (define bs blob-size)
  (define gs guid-size)
  (define (ci key) (hash-ref coded-index-sizes key))
  (make-hash
   `(('assembly
     (hash-alg . 4)
     (major . 4)
     (minor . 4)
     (build . 2)
     (revision . 2)
     (flags . 4)
     (pk . ,bs)
     (name . ,ss)
     (culture . ,ss)
     (test ,(ci 'typedef))
     )
    )))

(define (parse-cli-metadata-stream md-root header rdr port)
  ; this is the big one!
  (define offset (hash-ref header 'offset))
  (define size (hash-ref header 'size))

  (define start (+ md-root offset))
  (file-position port start)

  (define reserved (read-bytes 4 port))
  (define major (read-bytes 1 port))
  (define minor (read-bytes 1 port))
  ; bit vector for heap sizes.
  ; these flags determine the size of the indexes that
  ; appear in all metadata tables 
  (define heap-sizes (read-u8-le port))
  
  (define string-size (if (bits-set? 1 heap-sizes) 4 2))
  (set-asm-reader-string-index-size! rdr string-size)

  (define guid-size (if (bits-set? 2 heap-sizes) 4 2))
  (set-asm-reader-guid-index-size! rdr guid-size)

  (define blob-size (if (bits-set? 4 heap-sizes) 4 2))
  (set-asm-reader-blob-index-size! rdr blob-size)
  
  (define reserved2 (read-bytes 1 port))
  ; bit vector of present tables
  (define valid (read-bytes 8 port))
  (define valid-int (bytes->uint-le valid))
  ; bit vector of sorted tables (II.24.2.6 Sorted)
  (define sorted (read-bytes 8 port))
  (set-asm-reader-sorted-mask! rdr (bytes->uint-le sorted))
  (set-asm-reader-cache! rdr (make-hasheq))

  ; calculate the number of present tables
  ; this is the number of bits set in valid.
  ; a maximum of x2C (44) tables.
  ; we can also record the order of the tables whilst we are at it.
  ; and, the next 4 bytes for each table is the amount of rows it
  ; holds, so we can also load that now!
  (define-values (table-count table-order)
    (let-values ([(count tables)
      (for/fold ([count 0]
                 [tables '()])
                ([i (in-range #x40)])
        (let* ([target (arithmetic-shift 1 i)]
               [masked (bitwise-and target valid-int)]
               [count1 (+ count 1)])
          (if (equal? target masked)
              (let ([type
                     (let ([t (table-by-id i)])
                       (if t
                           (table-name t)
                           (error 'read-file "unknown cli metadata table 0x~x" i)))])
                (values count1 (cons (table-data type (read-u32-le port) count) tables)))
                    
              (values count tables))))])
      (values count (reverse tables))))
  (when (bits-set? #x40 heap-sizes)
    ; II.24.2.6 does not define this field. SRM (ReadMetadataTableHeader) reads
    ; and ignores 4 bytes here when HeapSizes.ExtraData is set.
    (read-bytes 4 port))
  (define table-start (file-position port))
  ; some encodings in the tables determine the amount
  ; of bytes used for an index depending on the maximum rows found in
  ; any of the tables it could be looking at.
  ; eg, a field might represent an index into typedef, typeref or typesec.
  ; it uses 3 bits to identify which table, and the rest of the index
  ; must have enough bits to locate a row in any of the 3 tables.
  ; II.24.2.6: simple and coded index widths come from the schema (schema.rkt).
  ; Absent tables have zero rows, so they never widen an index.
  (define tables
    (for/hash ([td table-order])
      (values (table-data-type td) td)))
  (define (rows-of name)
    (let ([td (hash-ref tables name #f)])
      (if td (table-data-row-count td) 0)))
  (define encodings (make-hash))
  (for ([td table-order])
    (hash-set! encodings (table-data-type td) (simple-index-width (table-data-row-count td))))
  (for ([k (in-list schema-coded-kinds)])
    (hash-set! encodings (coded-kind-name k) (coded-index-width k rows-of)))
  (set-asm-reader-table-attributes! rdr tables)
  (set-asm-reader-encoding-sizes! rdr encodings)
  
  ;now we have everything we need to calculate the size of each table row,
  ;and therefore the actual size and offset of each table.
  (define end-address
    (for/fold
     ([address table-start])
     ([table table-order])
      (let* ([count (table-data-row-count table)]
             [t (table-by-name (table-data-type table))]
             [size (row-size t string-size blob-size guid-size rows-of)])
        (set-table-data-start-offset! table address)
        (set-table-data-row-size! table size)
        (+ address (* size count)))))

  #;(writeln (format "total ~a"
                   ( apply + (map (λ (x) (* (table-data-row-size x) (table-data-row-count x))) table-order))
                   ))
  
  (make-hash
   `(
     (reserved ,@reserved)
     (major ,@major)
     (minor ,@minor)
     (heap-sizes ,@heap-sizes)
     (reserved2 ,@reserved2)
     (valid ,@valid)
     (valid-int ,@valid-int)
     (sorted ,@sorted)
     (sorted-int ,@(bytes->uint-le sorted))
     (table-count ,@table-count)
     (tables ,@table-order)
     (tablemet ,@tables)
     (encodings ,@encodings)
     )))


; maps a stream name to the key we keep it under, or #f for streams we skip.
; ECMA-335 II.24.2.2 lists the names. SRM also skips unknown streams
; (MetadataReader.cs, the default: continue case), so we do the same.
(define (cli-stream-key name)
  (cond
    ; blobs are encoded signatures for things like methods.
    ; we need to parse these for the type system 
    [(equal? "#Blob" name) 'blob]
    ; all non user strings, we need this!
    [(equal? "#Strings" name) 'strings]
    ; user strings in utf16 wide. don't need at the moment
    [(equal? "#US" name) 'us]
    ; guids not really used, don't need it for reading metadata
    [(equal? "#GUID" name) 'guid]
    ; this stream is the most complex one that has the relational
    ; tables that represent all the types, emitted il, and all other
    ; metadata. #- is the uncompressed form of the same tables (II.24.2.6).
    [(member name '("#~" "#-")) '~]
    [else #f]))

(define (parse-cli-metadata md-root rdr port)
  (file-position port md-root)
  (define sig (read-bytes 4 port))
  (define major (read-bytes 2 port))
  (define minor (read-bytes 2 port))
  (define reserved (read-bytes 4 port))
  ; version string is padded to a multiple of four
  (define length (read-bytes 4 port))
  (define version (read-bytes (bytes->uint-le length) port))
  (define flags (read-bytes 2 port)) ;always 0
  (define num-streams (read-bytes 2 port))
  ;now follows num-streams array of StreamHeader structs
  (define headers 
    (for*/hash ([i (in-range (bytes->uint-le num-streams))]
                [header (in-value (parse-cli-stream-header port))]
                [key (in-value (cli-stream-key (bytes->string/latin-1 (hash-ref header 'name))))]
                #:when key)
      (values key header)))

  ;we copy and store the entire heaps as bytestring.  
  (define string-heap
    (let* ([head (hash-ref headers 'strings)]
          [offset (hash-ref head 'offset)]
          [size (hash-ref head 'size)])         
   (subbytes
    (asm-reader-raw rdr)
    (+ md-root offset)
    (+ md-root offset size))))
  
  (set-asm-reader-string-heap! rdr string-heap)

  ; #US is optional, so an absent one reads as an empty heap.
  (set-asm-reader-us-heap!
   rdr
   (let ([head (hash-ref headers 'us #f)])
     (if head
         (let* ([offset (hash-ref head 'offset)]
                [size (hash-ref head 'size)])
           (subbytes
            (asm-reader-raw rdr)
            (+ md-root offset)
            (+ md-root offset size)))
         #"")))

  (set-asm-reader-blob-heap!
   rdr
   (let* ([head (hash-ref headers 'blob)]
          [offset (hash-ref head 'offset)]
          [size (hash-ref head 'size)])         
   (subbytes
    (asm-reader-raw rdr)
    (+ md-root offset)
    (+ md-root offset size))))

  (set-asm-reader-guid-heap!
   rdr
   (let* ([head (hash-ref headers 'guid)]
          [offset (hash-ref head 'offset)]
          [size (hash-ref head 'size)])         
   (subbytes
    (asm-reader-raw rdr)
    (+ md-root offset)
    (+ md-root offset size))))

  (define (string-lookup offset)
    (define (aux start offset)
      (cond       
        [(equal? (bytes-ref string-heap (+ start offset)) 0)
         ; end of string
         (bytes->string/utf-8 (subbytes string-heap start (+ start offset)))]       
        [else (aux start (+ offset 1))])) 
    (aux offset 0))
  (set-asm-reader-get-string! rdr string-lookup)

  ;now we can parse the big metadata stream of tables.
  ;we don't want to perform a full (slow) parse, though.
  ;instead, we'll work out which tables are present, their row counts,
  ;and from that we can determine the size of various indexes.
  ;that will let us calculate the size of a row for each table, which
  ;will let us calculate the offset where each table begins.
  ;this will let the caller jump around to the table and row they want,
  ;and only then will we actually parse any of it.
  (define tables (parse-cli-metadata-stream md-root (hash-ref headers '~) rdr port))
  (make-hash
   `(
     (sig ,@sig)
     (major ,@major)
     (minor ,@minor)
     (reserved ,@reserved)
     (length ,@length)
     (version ,@version)
     (flags ,@flags)
     (num-streams ,@num-streams)
     (headers ,@headers)
     (tables ,@tables)
     ;(strings ,@strings)
     ;(metadata ,@(parse-cli-metadata-stream md-root (hash-ref headers '~) string-lookup port))
     )


   )
  )

(define (read-file filename)
  ;(time
   (define rdr (asm-reader))
   (set-asm-reader-filename! rdr filename)
   ; one exact-size read: port->bytes grows a buffer and costs about 8x more on mscorlib
   (define all-bytes (call-with-input-file filename (λ (in) (read-bytes (file-size filename) in))))
   (set-asm-reader-raw! rdr all-bytes)
   (define port (open-input-bytes all-bytes)) ;binary default

   (define pe-headers (read-pe-headers port))
   (set-asm-reader-resolve-rva! rdr (λ (rva) (rva->file-offset pe-headers rva)))

;;    (for ([k (hash-keys (hash-ref hash 'pe-opt))])
;;      (writeln k))
;;    
   ;there's 4 tables but we only care about the cli header when reading

;;    (writeln (format "cli header : ~x" (calc-file-pos (to-int (hash-ref (hash-ref hash 'pe-opt) 'cli-header-table-rva)))))
;;    (writeln (format "iat table : ~x" (calc-file-pos (to-int (hash-ref (hash-ref hash 'pe-opt) 'iat-table-rva)))))
;;    (writeln (format "base reloc table : ~x" (calc-file-pos (to-int (hash-ref (hash-ref hash 'pe-opt) 'base-reloc-table-rva)))))
;;    (writeln (format "import table : ~x" (calc-file-pos (to-int (hash-ref (hash-ref hash 'pe-opt) 'import-table-rva)))))
   ;cli header
   (define cli-header
     (begin (file-position port (rva->file-offset pe-headers (bytes->uint-le (hash-ref (hash-ref pe-headers 'pe-opt) 'cli-header-table-rva))))
            (read-spec cli-header-spec port)))

;;    (writeln (format "cli metadata : ~x" (calc-file-pos (to-int (hash-ref cli-header 'metadata-rva)))))
   ;now onto the cli metadata itself
   (define md-root (rva->file-offset pe-headers (bytes->uint-le (hash-ref cli-header 'metadata-rva))))
   (set-asm-reader-metadata-root! rdr md-root)
   (define cli-meta
     (parse-cli-metadata md-root rdr port))
      
   ;(writeln cli-meta)
   ;the rest gets more complex and is handled in other functions
   ;(writeln (format "ended at location 0x~X ~a" (file-position port)(file-position port)))
   ;(hash-count (hash-ref cli-meta 'strings))
   ;cli-meta
   rdr

;  )
)

   

(define (parse-assembly-row rdr port)
  (define ss (asm-reader-string-index-size rdr))
  (define bs (asm-reader-blob-index-size rdr))
  (define hash-alg (read-u32-le port))
  (define major (read-u16-le port))
  (define minor (read-u16-le port))
  (define build (read-u16-le port))
  (define revision (read-u16-le port))
  (define flags (read-u32-le port))
  (define public-key-index (read-uint-le bs port))
  (define name-index (read-uint-le ss port))
  (define culture-index (read-uint-le ss port))

  ((asm-reader-get-string rdr) name-index)
  ;#t
  )

(define (get-public-typedefs rdr)
  (hash-ref! (asm-reader-cache rdr) 'public-typedefs (λ () (scan-public-typedefs rdr))))

(define (scan-public-typedefs rdr)
  ; we need this to be as fast as possible so we'll write a manual version.
  ; the first 4 bytes are the TypeAttributes, and the first bit is set if the
  ; type is public.  because it is little-endian, that is the fist byte in the
  ; row.  we can read that, check the bit, and skip the rest of the row if not.
  (define td (hash-ref (asm-reader-table-attributes rdr) 'typedef))
  (define offset (table-data-start-offset td))
  (define size (table-data-row-size td))
  (define rows (table-data-row-count td))
  (define raw (asm-reader-raw rdr))
  (define ss (asm-reader-string-index-size rdr))
  (define sl (asm-reader-get-string rdr))
  (define (aux acc index row-count)
    (cond
      [(equal? row-count rows) acc]
      ; visibility is the low 3 bits of the flags. only Public (1) is a top level public type;
      ; the nested visibilities share bit 0 with it, so the whole field must be compared
      [(equal? (bitwise-and (bytes-ref raw index) 7) 1)
        (begin
          ; the name string begins 4 bytes later followed by the namespace string
          ; don't resolve them yet to avoid cache misses in the (potentially) big bytestring
          (let* ([name (+ index 4)]
                [ns (+ name ss)]
                [acc (cons
                      (cons (bytes->uint-le (subbytes raw name (+ name ss)))
                            (bytes->uint-le (subbytes raw ns (+ ns ss))))
                      acc)])
            (aux acc (+ index size) (+ row-count 1))))]
      [else
        (aux acc (+ index size) (+ row-count 1))]))
  
  (define types (aux (list) offset 0))

  ;now resolve them
  (map (λ (x)
         (let ([n (car x)]
               [ns (cdr x)])
           (cons (sl n) (sl ns)))) types))

; returns #f when the image has no assembly table (e.g. a netmodule)
(define (read-assembly-meta rdr)
  (define td (hash-ref (asm-reader-table-attributes rdr) 'assembly #f))
  (and td
       (let ([port (open-input-bytes (asm-reader-raw rdr))])
         (file-position port (table-data-start-offset td))
         (parse-assembly-row rdr port))))

; generic row decoder, 1-based rid. returns a vector with one entry per column:
;   u8/u16/u32 -> integer, string -> string, guid -> 16 bytes (#f when null),
;   blob -> bytes without its length prefix (#f when null),
;   (index t) -> rid (0 when null), (coded k) -> (cons target-name rid) (#f when null).
(define (read-row rdr name rid)
  (define layout (table-layout rdr name))
  (define base (row-offset rdr layout name rid))
  (for/vector #:length (vector-length (layout-columns layout))
              ([c (in-vector (layout-columns layout))])
    (decode-column rdr c (raw-uint (asm-reader-raw rdr) (+ base (col-offset c)) (col-width c)))))

; One column of a table as laid out in this image: its byte offset in the row, its width, and
; its schema kind. coded is the coded-kind for a (coded k) column, else #f.
(struct col (name offset width kind coded))
; A table's columns, its row size and count, and where its rows start in the raw bytes.
(struct layout (columns by-name start size count))

; The layout of a table, computed once per reader (II.24.2.6 row layout from schema.rkt).
; Raises when the table is unknown or absent.
(define (table-layout rdr name)
  (define cache (hash-ref! (asm-reader-cache rdr) 'layouts make-hasheq))
  (or (hash-ref cache name #f)
      (let* ([t (or (table-by-name name) (error 'read-row "unknown table ~a" name))]
             [td (or (hash-ref (asm-reader-table-attributes rdr) name #f)
                     (error 'read-row "table ~a is not present" name))]
             [ss (asm-reader-string-index-size rdr)]
             [bs (asm-reader-blob-index-size rdr)]
             [gs (asm-reader-guid-index-size rdr)]
             [rows-of (λ (n) (table-row-count rdr n))]
             [cols (for/fold ([acc '()] [offset 0] #:result (list->vector (reverse acc)))
                             ([c (in-list (table-columns t))])
                     (define kind (column-kind c))
                     (define width (column-width kind ss bs gs rows-of))
                     (values (cons (col (column-name c) offset width kind
                                        (and (pair? kind) (eq? (car kind) 'coded)
                                             (coded-kind-by-name (cadr kind))))
                                   acc)
                             (+ offset width)))]
             [l (layout cols
                        (for/hasheq ([c (in-vector cols)] [i (in-naturals)]) (values (col-name c) i))
                        (table-data-start-offset td) (table-data-row-size td)
                        (table-data-row-count td))])
        (hash-set! cache name l)
        l)))

(define (row-offset rdr l name rid)
  (unless (and (exact-integer? rid) (<= 1 rid (layout-count l)))
    (error 'read-row "row ~a out of range for ~a" rid name))
  (+ (layout-start l) (* (- rid 1) (layout-size l))))

; Rows in a table, 0 when it is absent.
(define (table-row-count rdr name)
  (define td (hash-ref (asm-reader-table-attributes rdr) name #f))
  (if td (table-data-row-count td) 0))

(define (raw-uint raw offset width)
  (case width
    [(1) (bytes-ref raw offset)]
    [(2) (integer-bytes->integer raw #f #f offset (+ offset 2))]
    [else (integer-bytes->integer raw #f #f offset (+ offset 4))]))

(define (layout-col rdr l name column)
  (cond
    [(exact-nonnegative-integer? column) (vector-ref (layout-columns l) column)]
    [(hash-ref (layout-by-name l) column #f) => (λ (i) (vector-ref (layout-columns l) i))]
    [else (error 'row-column "~a has no column ~a" name column)]))

; The undecoded value of one column, read straight from the raw bytes: a heap offset, a rid, or
; an encoded coded index (II.24.2.6). column is a schema column name or a 0-based position.
; Sorted tables are ordered by these raw values, so binary searches compare them.
(define (row-column-raw rdr name rid column)
  (define l (table-layout rdr name))
  (define c (layout-col rdr l name column))
  (raw-uint (asm-reader-raw rdr) (+ (row-offset rdr l name rid) (col-offset c)) (col-width c)))

; One column decoded as read-row decodes it.
(define (row-column rdr name rid column)
  (define l (table-layout rdr name))
  (define c (layout-col rdr l name column))
  (decode-column rdr c
                 (raw-uint (asm-reader-raw rdr) (+ (row-offset rdr l name rid) (col-offset c))
                           (col-width c))))

(define (decode-column rdr c value)
  (define kind (col-kind c))
  (cond
    [(symbol? kind)
     (case kind
       [(string) ((asm-reader-get-string rdr) value)]
       [(guid) (if (zero? value)
                   #f
                   (subbytes (asm-reader-guid-heap rdr) (* (- value 1) 16) (* value 16)))]
       [(blob) (blob-at (asm-reader-blob-heap rdr) value)]
       [else value])]
    [(col-coded c)
     (if (zero? value)
         #f
         (let-values ([(target rid) (coded-decode (col-coded c) value)])
           (unless target (error 'read-row "unused tag in ~a" (cadr kind)))
           (cons target rid)))]
    [else value]))

; II.24.2.4: a blob is prefixed by its compressed length
(define (blob-at heap index)
  (if (zero? index)
      #f
      (let* ([b0 (bytes-ref heap index)]
             [len-size (cond [(zero? (bitwise-and b0 #x80)) 1]
                             [(= (bitwise-and b0 #xC0) #x80) 2]
                             [else 4])]
             [len (for/fold ([acc (bitwise-and b0 (case len-size [(1) #x7F] [(2) #x3F] [else #x1F]))])
                            ([i (in-range 1 len-size)])
                    (+ (* acc 256) (bytes-ref heap (+ index i))))]
             [start (+ index len-size)])
        (subbytes heap start (+ start len)))))

; Hot-path access for index.rkt: fetch a layout once, then read raw columns with no lookups and
; no range check. rid must be in 1..(layout-count l).
(define (layout-column-index l column)
  (or (hash-ref (layout-by-name l) column #f) (error 'layout "no column ~a" column)))

(define (layout-raw rdr l rid i)
  (define c (vector-ref (layout-columns l) i))
  (raw-uint (asm-reader-raw rdr) (+ (layout-start l) (* (- rid 1) (layout-size l)) (col-offset c))
            (col-width c)))

; True when the header's Sorted mask marks the table as sorted (II.24.2.6).
(define (table-sorted? rdr name)
  (define t (table-by-name name))
  (and t (bitwise-bit-set? (or (asm-reader-sorted-mask rdr) 0) (table-id t))))

; Reads the bytes of a bare metadata root (the BSJB block that metadata-chunk writes), with
; offsets relative to byte 0. Like read-file, this returns a fresh reader with empty caches.
(define (read-metadata-root bs)
  (define rdr (asm-reader))
  (set-asm-reader-raw! rdr bs)
  (set-asm-reader-metadata-root! rdr 0)
  (parse-cli-metadata 0 rdr (open-input-bytes bs))
  rdr)

;(define parsed (read-file "c:/temp/nano2.exe"))
;parsed
;(define parsed (read-file  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll"))
;(define sl (asm-reader-get-string parsed))rb
;(asm-reader-table-attributes parsed)
;((asm-reader-get-string parsed) #x4AE21)
#;(time
  (let* ([td (hash-ref (asm-reader-table-attributes parsed) 'assembly)]
         [offset (table-data-start-offset td)]
         [port (open-input-bytes (asm-reader-raw parsed))])
    (file-position port offset)
    (parse-assembly-row parsed port)))
#;(time
 (define x (get-public-typedefs parsed))
 (assoc "RegistryValueKind" x)
;x
 )
;(hash-ref parsed 'tablemet)
