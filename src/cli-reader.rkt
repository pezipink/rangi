#lang racket/base
(require racket/string)
(require racket/port)
; read-only accessors for tests that decode table rows. row decoding stays out of the reader,
; so the lazy path used by the macro expander is unchanged.
(provide read-file get-public-typedefs read-assembly-meta
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

; unsigned little-endian conversion
(define (to-int bytes) (integer-bytes->integer bytes #f #f))

; unsigned big-endian conversion
(define (to-int-be bytes) (integer-bytes->integer bytes #f #t))

; default little-endian unsigned for most binary data
(define (read-int size port) (to-int (read-bytes size port)))


(define (cli-decompress-unsigned port)
  ;to decompress we acccept a port that starts with
  ;the big-endian bytes. note that they are written inside
  ;the PE file big-endian so we can tell with the first byte,
  ;how many bytes there are.
  ;unlike everything else in a PE which is little-endian
  (define first (read-byte port))  
  (cond
    [(equal? (bitwise-and first #xC0) #xC0)         
     (let ([second (read-byte port)]
           [third (read-byte port)]
           [fourth (read-byte port)])       
       (bitwise-ior
        (arithmetic-shift (bitwise-and #x3F first) 24)
        (arithmetic-shift second 16)
        (arithmetic-shift third 8)
        fourth))]
    
    [(equal? (bitwise-and first #x80) #x80)
     (let ([second (read-byte port)])
           (bitwise-ior
            (arithmetic-shift (bitwise-and #x7F first) 8)
            second))]
    
    [else first]))


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
  
  

; only the first 0x40 bytes are needed; e_lfanew at 0x3C points at the PE header
(define ms-dos-header-spec
  '((header 64)))

(define pe-file-header-spec
  '(
    (sig 4)
    (machine 2)
    (num-secs 2)
    (stamp 4)
    (sym 4)
    (num-sym 4)
    (opt-header-size 2)
    (characteristics 2)))

(define pe-opt-header-spec
  '(
    ; standard fields
    (magic 2)
    (lmajor 1)
    (lminor 1)
    (code-size 4)
    (init-data-size 4)
    (uninit-data-size 4)
    (entry-rva 4)
    (base-code 4)
    (base-data 4)
    ; nt specific fields
    (image-base 4)
    (section-align 4)
    (file-align 4)
    (os-major 2)
    (os-minor 2)
    (user-major 2)
    (user-minor 2)
    (subsys-major 2)
    (subsys-minor 2)
    (reserved 4)
    (image-size 4)
    (header-size 4)
    (file-checksum 4)
    (subsys 2)
    (dll-flags 2)
    (stack-reserve 4)
    (stack-commit 4)
    (heap-reserve 4)
    (heap-commit 4)
    (loader-flags 4)
    (num-data-dirs 4)
    ; there's always 16 data directories
    ;8 bytes encode rva and size of each
    ; only 4 actually exist
    (export-table 8)
    (import-table-rva 4) ;exists
    (import-table-size 4) ;exists
    (resource-table 8)
    (exception-table 8)
    (certificate-table 8)
    (base-reloc-table-rva 4);exists
    (base-reloc-table-size 4);exists
    (debug-table 8)
    (copyright-table 8)
    (global-ptr-table 8)
    (tls-table 8)
    (config-table 8)
    (bound-import-table 8)
    (iat-table-rva 4);exists
    (iat-table-size 4);exists    
    (delay-import-table 8)
    (cli-header-table-rva 4);exists
    (cli-header-table-size 4);exists
    (reserved-table 8)

    ))

; PE32+ drops BaseOfData and widens ImageBase and the stack and heap sizes to 8 bytes
(define pe32plus-opt-header-spec
  (map (λ (x)
         (case (car x)
           [(image-base stack-reserve stack-commit heap-reserve heap-commit) (list (car x) 8)]
           [else x]))
       (filter (λ (x) (not (eq? (car x) 'base-data))) pe-opt-header-spec)))

(define pe-section-header-spec
  '(
   (name 8)
   (virt-size 4)
   (virt-address 4)
   (size-raw 4)
   (ptr-raw 4)
   (ptr-reloc 4)
   (ptr-linenum 4)
   (num-reloc 2)
   (num-linenum 2)
   (characteristics 4)))

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

(define (read-spec spec port)
  (make-hash
   (map (λ (x) (let ([id (car x)]
                     [size (cadr x)])
                 (cons id (read-bytes size port)))) spec)))

(define (parse-cli-stream-header port)
  ; offset to start of stream from metadata root
  (define offset (read-int 4 port))
  (define size (read-int 4 port))
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
  (define heap-sizes (to-int (read-bytes 1 port)))
  
  (define string-size (if (bits-set? 1 heap-sizes) 4 2))
  (set-asm-reader-string-index-size! rdr string-size)

  (define guid-size (if (bits-set? 2 heap-sizes) 4 2))
  (set-asm-reader-guid-index-size! rdr guid-size)

  (define blob-size (if (bits-set? 4 heap-sizes) 4 2))
  (set-asm-reader-blob-index-size! rdr blob-size)
  
  (define reserved2 (read-bytes 1 port))
  ; bit vector of present tables
  (define valid (read-bytes 8 port))
  (define valid-int (to-int valid))
  ; bit vector of sorted tables (not sure about this? the spec doesn't describe it?)
  (define sorted (read-bytes 8 port))

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
                     (case i
                       [(#x0) 'module]
                       [(#x1) 'typeref]
                       [(#x2) 'typedef]
                       [(#x4) 'field]
                       [(#x6) 'methoddef]
                       [(#x8) 'param]
                       [(#x9) 'interfaceimpl]
                       [(#xA) 'memberref]
                       [(#xB) 'constant]
                       [(#xC) 'customattribute]
                       [(#xD) 'fieldmarshal]
                       [(#xE) 'declsecurity]
                       [(#xF) 'classlayout]
                       [(#x10) 'fieldlayout]
                       [(#x11) 'standalonesig]
                       [(#x12) 'eventmap]
                       [(#x14) 'event]
                       [(#x15) 'propertymap]
                       [(#x17) 'property]
                       [(#x18) 'methodsemantics]
                       [(#x19) 'methodimpl]
                       [(#x1A) 'moduleref]
                       [(#x1B) 'typespec]
                       [(#x1C) 'implmap]
                       [(#x1D) 'fieldrva]                       
                       [(#x20) 'assembly]
                       [(#x23) 'assemblyref]
                       [(#x26) 'file]
                       [(#x27) 'exportedtype]
                       [(#x28) 'manifestresource]
                       [(#x29) 'nestedclass]
                       [(#x2A) 'genericparam]
                       [(#x2B) 'methodspec]
                       [(#x2C) 'genericparamconstraint]
                       [(#x03) 'fieldptr]
                       [(#x05) 'methodptr]
                       [(#x07) 'paramptr]
                       [(#x13) 'eventptr]
                       [(#x16) 'propertyptr]
                       [(#x1E) 'enclog]
                       [(#x1F) 'encmap]
                       [(#x21) 'assemblyprocessor]
                       [(#x22) 'assemblyos]
                       [(#x24) 'assemblyrefprocessor]
                       [(#x25) 'assemblyrefos]
                       [else (error 'read-file "unknown cli metadata table 0x~x" i)]
                       )])
                (values count1 (cons (table-data type (read-int 4 port) count) tables)))
                    
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
  (define (max-rows-lookup to-search)
    (for/fold ([max 0])
              ([table table-order])
    (let ([type (table-data-type table)]
          [rows (table-data-row-count table)])
      (if (member type to-search)
          (if (> rows max) rows max)
          max))))

  ; the first set of encodings are just for simple table lookups.
  ; in this case if the table has more rows than will fit into
  ; 16 bits, then they are encoded with 32 bits, else 16 bits
  (define encodings (make-hash))
  (for ([td table-order])
    (hash-set! encodings (table-data-type td) (if (<= (table-data-row-count td) #xFFFF) 2 4)))

  ; now we have each of the special encodings that might look at more than one table.
  ; the lower bits are used to determine which table it actually is, and therefore
  ; those bits cannot be used to store the actual value. so the smaller 2 byte representation
  ; will be where the max row count of the biggest table fits into the remaining bits.
  ; 1 bit 
  (hash-set! encodings 'hasfieldmarshal (if (<= (max-rows-lookup '(field param)) #x7FFF) 2 4))
  (hash-set! encodings 'hassemantics (if (<= (max-rows-lookup '(event property)) #x7FFF) 2 4))
  (hash-set! encodings 'methoddeforref (if (<= (max-rows-lookup '(methoddef memberref)) #x7FFF) 2 4))
  (hash-set! encodings 'memberforwarded (if (<= (max-rows-lookup '(field methoddef)) #x7FFF) 2 4))
  (hash-set! encodings 'typeormethoddef (if (<= (max-rows-lookup '(typedef methoddef)) #x7FFF) 2 4))
  ; 2 bits
  (hash-set! encodings 'typedeforref (if (<= (max-rows-lookup '(typedef typeref typespec)) #x3FFF) 2 4)) 
  (hash-set! encodings 'hasconstant (if (<= (max-rows-lookup '(field param property)) #x3FFF) 2 4))
  (hash-set! encodings 'hasdeclsecurity (if (<= (max-rows-lookup '(typedef methoddef assembly)) #x3FFF) 2 4))
  (hash-set! encodings 'implementation (if (<= (max-rows-lookup '(file assemblyref exportedtype)) #x3FFF) 2 4)) 
  (hash-set! encodings 'resolutionscope (if (<= (max-rows-lookup '(module moduleref assemblyref typeref)) #x3FFF) 2 4)) 
  ; 3 bits
  (hash-set! encodings 'memberrefparent (if (<= (max-rows-lookup '(typedef typeref moduleref methoddef typespec)) #x1FFF) 2 4))
  ;  note this one has 3 'not used' tables in its tag encoding
  (hash-set! encodings 'customattributetype (if (<= (max-rows-lookup '(methoddef memberref)) #x1FFF) 2 4))
  
  ; 5 bits
  (hash-set!
   encodings
   'hascustomattribute
   (if (<= (max-rows-lookup
            '(methoddef field typeref typedef param interfaceimpl memberref module
              declsecurity property event standalonesig moduleref typespec assembly
               assemblyref file exportedtype manifestresource genericparam
              genericparamconstraint methodspec))
            #x7FF) 2 4)) ; 5 bits
  
  (define tables 
    (for/hash ([td table-order])
      (values (table-data-type td) td)))
  (set-asm-reader-table-attributes! rdr tables)
  (set-asm-reader-encoding-sizes! rdr encodings)
  
  ;now we have everything we need to calculate the size of each table row,
  ;and therefore the actual size and offset of each table.
  (define (calc-size items)
    (apply
     +
     (map (λ (x)
            (if (symbol? x)
                ; an absent table has no rows, so a 2 byte simple index is correct for it
                (hash-ref encodings x 2)
                x)) items)))
  
  ;todo: not sure to use spec approach yet
  ;(define specs (gen-table-specs string-size guid-size blob-size encodings))
  ;(writeln specs)
  
  ;(writeln (format "metadata start ~a" (file-position port)))
  (define end-address
    (let ([ss string-size]
          [gs guid-size]
          [bs blob-size])
      (for/fold
       ([address table-start])
       ([table table-order])
        (let* ([type (table-data-type table)]
               [count (table-data-row-count table)]            
               [row-size
                (calc-size
                 (case type
                   ['module (list 2 ss gs gs gs)]
                   ['typeref (list 'resolutionscope ss ss)]
                   ['typedef (list 4 ss ss 'typedeforref 'field 'methoddef)]
                   ['field (list 2 ss bs)]
                   ['methoddef (list 4 2 2 ss bs 'param)]
                   ['param (list 2 2 ss)]
                   ['interfaceimpl (list 'typedef 'typedeforref)]
                   ['memberref (list 'memberrefparent ss bs)]
                   ['constant (list 1 1 'hasconstant bs)]
                   ['customattribute (list 'hascustomattribute 'customattributetype bs)]
                   ['fieldmarshal (list 'hasfieldmarshal bs)]
                   ['declsecurity (list 2 'hasdeclsecurity bs)]
                   ['classlayout (list 2 4 'typedef)]
                   ['fieldlayout (list 4 'field)]
                   ['eventmap (list 'typedef 'event)]
                   ['event (list 2 ss 'typedeforref)]
                   ['propertymap (list 'typedef 'property)]
                   ['property (list 2 ss bs)]
                   ['methodsemantics (list 2 'methoddef 'hassemantics)]
                   ['methodimpl (list 'typedef 'methoddeforref 'methoddeforref)]
                   ['moduleref (list ss)]
                   ['typespec (list bs)]
                   ['implmap (list 2 'memberforwarded ss 'moduleref)]
                   ['fieldrva (list 4 'field)]
                   ['assembly (list 4 2 2 2 2 4 bs ss ss)]
                   ['assemblyref (list 2 2 2 2 4 bs ss ss bs)]
                   ['file (list 4 ss bs)]
                   ['exportedtype (list 4 4 ss ss 'implementation)]
                   ['manifestresource (list 4 4 ss 'implementation)]
                   ['nestedclass (list 'typedef 'typedef)]
                   ['genericparam (list 2 2 'typeormethoddef ss)]
                   ['methodspec (list 'methoddeforref bs)]
                   ['genericparamconstraint (list 'genericparam 'typedeforref)]
                   ['fieldptr (list 'field)]
                   ['methodptr (list 'methoddef)]
                   ['paramptr (list 'param)]
                   ['eventptr (list 'event)]
                   ['propertyptr (list 'property)]
                   ['standalonesig (list bs)]
                   ['enclog (list 4 4)]
                   ['encmap (list 4)]
                   ['assemblyprocessor (list 4)]
                   ['assemblyos (list 4 4 4)]
                   ['assemblyrefprocessor (list 4 'assemblyref)]
                   ['assemblyrefos (list 4 4 4 'assemblyref)]
                   [else (error 'read-file "unknown type ~a" type)]))]
               )
          (set-table-data-start-offset! table address)        
          (set-table-data-row-size! table row-size)
          (+ address (* row-size count))))))

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
     (sorted-int ,@(to-int sorted))
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
  (define version (read-bytes (to-int length) port))
  (define flags (read-bytes 2 port)) ;always 0
  (define num-streams (read-bytes 2 port))
  ;now follows num-streams array of StreamHeader structs
  (define headers 
    (for*/hash ([i (in-range (to-int num-streams))]
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
   (define all-bytes (call-with-input-file filename port->bytes))
   (set-asm-reader-raw! rdr all-bytes)
   (define port (open-input-bytes all-bytes)) ;binary default

   ;todo; we can skip some of the pe header
   (define dos-header (read-spec ms-dos-header-spec port))
   ; e_lfanew is the file offset of the PE signature
   (define pe-offset (to-int (subbytes (hash-ref dos-header 'header) #x3C #x40)))
   (file-position port pe-offset)
   (define pe-headers (make-hash))
   (hash-set! pe-headers 'ms-dos dos-header)
   (hash-set! pe-headers 'pe (read-spec pe-file-header-spec port))
   (define opt-start (file-position port))
   (define opt-header-size (to-int (hash-ref (hash-ref pe-headers 'pe) 'opt-header-size)))
   ; the magic tells PE32 and PE32+ apart
   (define magic (to-int (peek-bytes 2 0 port)))
   (hash-set! pe-headers 'pe-opt
              (read-spec (if (= magic #x20B) pe32plus-opt-header-spec pe-opt-header-spec) port))
   ; section headers follow the optional header, whose real size is recorded in the file header
   (file-position port (+ opt-start opt-header-size))
   
   ; at this point we have read all the static header data, now there will be a number of section
   ; headers as per pe-num-secs which we will stick in a list
   (define num-secs
     (to-int (hash-ref (hash-ref pe-headers 'pe) 'num-secs)))
   (define section-headers
     (for/list ([i (in-range 0 num-secs)]) (read-spec pe-section-header-spec port))) 
   ;after this there is padding until the first section data as pointed to by
   ;sec-header-ptr-raw (0x200 in example app)
   ;to determine what lies in each section, we need to do some calcs.
   ;for our 4 tables (import, reloc, cli, iat) we can determine which section they are in
   ;by looking at their rva, and comparing to each section's rva.
   ;for example, .text is at 0x2000 (sec-header-virt-address) with size 0x1d4 (sec-header-virt-address)
   ;for a size of 0x21d4.
   ;table cli has an rva of 0x2008 which is less than 0x21d4 and so lies within .text.
   ;it's actual address in the file is   (sec-header-ptr-raw .text)+(cli-rva - sec-header-virt-address)
   ;or, (0x200 + (0x2000 - 0x2008)) = 0x208
   ; of course, we need to search from the lowest address section first.
   (define (calc-file-pos rva)
     (or (for/first ([header section-headers]
                     #:when (let ([va (to-int (hash-ref header 'virt-address))])
                              (and (<= va rva) (< rva (+ va (to-int (hash-ref header 'virt-size)))))))
           (+ (to-int (hash-ref header 'ptr-raw)) (- rva (to-int (hash-ref header 'virt-address)))))
         (error 'read-file "rva 0x~x is not in any section" rva)))
   (set-asm-reader-resolve-rva! rdr calc-file-pos)

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
     (begin (file-position port (calc-file-pos (to-int (hash-ref (hash-ref pe-headers 'pe-opt) 'cli-header-table-rva))))
            (read-spec cli-header-spec port)))

;;    (writeln (format "cli metadata : ~x" (calc-file-pos (to-int (hash-ref cli-header 'metadata-rva)))))
   ;now onto the cli metadata itself
   (define md-root (calc-file-pos (to-int (hash-ref cli-header 'metadata-rva))))
   (set-asm-reader-metadata-root! rdr md-root)
   (define cli-meta
     (parse-cli-metadata md-root rdr port))
      
   ;(writeln cli-meta)
   ;the rest gets more complex and is handled in other functions
   (hash-set! pe-headers 'sec-headers section-headers)

   ;(writeln (format "ended at location 0x~X ~a" (file-position port)(file-position port)))

   ;(hash-count (hash-ref cli-meta 'strings))
   ;cli-meta
   rdr

;  )
)

   

(define (parse-assembly-row rdr port)
  (define ss (asm-reader-string-index-size rdr))
  (define bs (asm-reader-blob-index-size rdr))
  (define hash-alg (read-int 4 port))
  (define major (read-int 2 port))
  (define minor (read-int 2 port))
  (define build (read-int 2 port))
  (define revision (read-int 2 port))
  (define flags (read-int 4 port))
  (define public-key-index (read-int bs port))
  (define name-index (read-int ss port))
  (define culture-index (read-int ss port))

  ((asm-reader-get-string rdr) name-index)
  ;#t
  )

(define (get-public-typedefs rdr)
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
                      (cons (to-int (subbytes raw name (+ name ss)))
                            (to-int (subbytes raw ns (+ ns ss))))
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
