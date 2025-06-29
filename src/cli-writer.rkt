#lang racket
(require racket/match)
(require racket/hash)
(require "cli-reader.rkt") 
(provide assemble parse-il)
(define nano2
  '(
    (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
    (.assembly donothing {})
    (.module nano2.exe)
    (.class (private auto ansi) <Module>           
            [
             (.method
              (public static) void main () (cil managed)
              {
               (.entrypoint)
               (.maxstack 8)
               (ldc.i 42)
            ;   (ldc.i 42)
             ;  (add)
               (call void (mscorlib System.Console) WriteLine (int32))
               (ret)     
               })
      
             ]

     
            )))

(struct asm-ref
  ([filename]
   [index]
   [name]
   [reader])
  )
(struct table-data
  ([type]
   [row-count]
   [ordinal]
   [row-size])
  #:mutable
  #:transparent)

(struct asm-builder
  ([asm-refs]
   ; one assembly builder only
   [asm-def]
   ; one module only
   [mod-def]
   
   [refs]
   [class-defs]
   )
  #:transparent
  #:mutable)


(struct meth-builder
  ([prefix-list]
   [ret-type]
   [type] ; keep the parent type here as well for easier processing later
   [name]
   [param-list]
   [suffix-list]
   [il-stream]
   [sig-index #:auto] ; this field is set later after blob encoding
   [table-index #:auto]
   [il-index #:auto]  ; set after assembly
   )
  #:mutable
  #:transparent)
(define (mb->key mb)
  ; key is name and types the same as a memref
  (list
   (meth-builder-ret-type mb)
   (meth-builder-type mb)
   (meth-builder-name mb)   
   (meth-builder-param-list mb)))
    
(struct class-builder
  ([name]
   [flags]
   [strings]
   ; hash - name -> meth-builder
   [meth-builders])
  #:mutable
  #:transparent
  )
         

(define (max-asm-ref-index asm)
  (define refs (asm-builder-asm-refs asm))
  (if (equal? (hash-count refs) 0)
      0
      (max (map (λ (ref) (asm-ref-index ref)) (hash-values refs)))))

  
(define (ref-assembly asm filename)
  (define max-index (max-asm-ref-index asm))
  (define index (if (number? max-index) (+ max-index 1) 1))
  (define reader (read-file filename))
  ;todo: currently this function returns only the name
  (define asm-name (read-assembly-meta reader))
  (hash-set! (asm-builder-asm-refs asm) asm-name (asm-ref filename max-index asm-name reader))
  
  asm)


(define (def-module asm name)
  ; there is only one assembly in an exe / dll
  (set-asm-builder-mod-def! asm name)
  (hash-set! (hash-ref (asm-builder-refs asm) 'string) (symbol->string name) #t)
  asm)

(define (def-assembly asm name)
  ;  there is only one module in an exe / dll
  (set-asm-builder-asm-def! asm name)
  (hash-set! (hash-ref (asm-builder-refs asm) 'string) (symbol->string name) #t)
  asm)
(define (parse-type type refs)
  (define s (hash-ref refs 'string))
  (define us (hash-ref refs 'us))
  (define tr (hash-ref refs 'typeref))
    
  (match type
    ; special types don't need their stuff captuing
    [(or 'void (list 'void)
         'object (list 'object)
         'int32 (list 'int32))      
     refs]
    [(list asm-name namespace-and-name)
     ; a fully qualified name with namespace is a typeref
     (define split (string-split (symbol->string namespace-and-name) "."))
     (for ([str split]) (hash-set! s str #t))
     (hash-set! s (symbol->string asm-name) #t)
     ; the entire thing is the key
     (hash-set! tr type #t)
     refs
     ]
    ))
(define (extract-refs refs il-stream)
  ; we can probably extract most stuf in a general matching manner,
  ; but some things we need to associate together. eg, a call
  ; contains the type ref / def but also the method details, and the method
  ; has to be related to the typedef.
  ; (call void (mscorlib System.Console) WriteLine (object))
  
  
  (for   
      ([node il-stream])
    (begin
      (define s (hash-ref refs 'string))
      (define us (hash-ref refs 'us))
      (define tr (hash-ref refs 'typeref))
      (define mr (hash-ref refs 'memref))
      (match node
        [(list 'call ret-type type method-name (list-rest param-list))
         (parse-type ret-type refs)
         (parse-type type refs)
         (for ([ty param-list]) (parse-type ty refs))
         (hash-set! s (symbol->string method-name) #t)
         (hash-set! mr (cons ret-type (cons type (cons method-name (list param-list)))) #t)
         refs]
        [else (void)])))

  )
(define (def-class asm flags name body)
  ;  root class in the module only, supported nested later
  (define cb (class-builder name flags (list) (make-hash)))
  (set-asm-builder-class-defs! asm (cons cb (asm-builder-class-defs asm)))
  (define refs (asm-builder-refs asm))
  (define s (hash-ref refs 'string))
  (hash-set! s (symbol->string name) #t)
  (for
      ([node body])
    (match node
      [(list '.method prefix-list ret-type meth-name param-list suffix-list il-stream)
       ; we can't assemble until until we know the size of the metadata tokens,
       ; and we won't know that until we know the size of all the metadata tables
       ; and the string/guid/blob heaps.  For now all we can do is scan the il
       ; and extract any strings, typerefs etc from it
       
       (hash-set! s (symbol->string meth-name) #t)
       (parse-type ret-type refs)
       (for ([t param-list]) (parse-type t refs))


       ; todo: we'll also need to collect the locals, maxstack, exceptions since they
       ;  determine the method header size.  i think we can encode everything as "fat" for now
       
       (extract-refs refs il-stream)
       
       
       (hash-set! (class-builder-meth-builders cb)
                  meth-name
                  (meth-builder
                   prefix-list
                   ret-type
                   name
                   meth-name
                   param-list
                   suffix-list
                   il-stream
                   ))
       
       ]))
            
  )

(define (parse-il program)
  (define
    acc (asm-builder
         (make-hash)
         #f #f
         (make-hash
          `((typeref ,@(make-hash))
            (string ,@(make-hash))
            (us ,@(make-hash))
            (memref ,@(make-hash))))
         (list)))
  (for   
      ([node program])
    (define s (hash-ref (asm-builder-refs acc) 'string))
    (match node
      [(list '.assembly 'extern filename body)
       (ref-assembly acc filename)]
    
      [(list '.assembly name body)
       (begin
         (unless (equal? (asm-builder-asm-def acc) #f)
           (raise "only one .assembly diretive is allowed"))
       
         (def-assembly acc name))]
    
      [(list '.module name)
       (begin
         (unless (equal? (asm-builder-mod-def acc) #f)
           (raise "only one .module diretive is allowed"))
         (def-module acc name))]
    
      [(list '.class flags name body)
       (begin
         (def-class acc flags name body)
       
         acc)]
    
      ))
  acc)

(define (wlf . args)
  ;(void)
  (writeln (apply format args))
  )

(define (cli-compress-unsigned num)
  (cond
    [(> num #x1FFFFFFF) (raise "cannot compress numbers greater than 29 bits")]
    [(<= num #x7F) (bytes num)]
    [(<= num #x3FF) (bytes (bitwise-ior #x80 (arithmetic-shift num -8)) (bitwise-and #xFF num))]
    [else (bytes
           (bitwise-ior #xC0 (arithmetic-shift num -24))
           (bitwise-and #xFF (arithmetic-shift num -16))
           (bitwise-and #xFF (arithmetic-shift num -8))
           (bitwise-and #xFF num) ) ]
    ))

(define (encode-type-blob type)
  (cond
    [(equal? 'object type) (bytes #x1C)]
    [(equal? 'int32 type) (bytes #x08)]
    [else (raise (format "encode-type-blob unhandled ~a" type))]))
  
(define (reduce f xs)
  (and (not (empty? xs)) (foldl f (first xs) (rest xs))))

(define (collect xs)
  (reduce append xs))

(define (encode-mr-blob mr)
  (match mr
    [(list ret-type type name param-list)
     (let([by1 (bytes #x0)] ; hasthis | explicthis | default (0) | vararg.  not supporting these yet, default 0 is good
          [count-encoded (cli-compress-unsigned (length param-list))]
          [ret-encoded
           ; todo: we don't support everything here yet
           ; missing custom mod, byref, typedbyref
           (cond
             [(equal? 'void ret-type) (bytes #x1)]
             [else (encode-type-blob ret-type)])
           ]
          [param-encoded (if (empty? param-list) (bytes )  (reduce bytes-append (map encode-type-blob param-list)))]
          )
       (bytes-append by1 count-encoded ret-encoded param-encoded)
       )]))
(define (encode-md-blob md)
  
  (define ret-type (meth-builder-ret-type md))
  (define param-list (meth-builder-param-list md))  
  
  ; the method def sig is actually the same as the ref one, except some difference for
  ; varargs which we do no yet support
  (let ([by1 (bytes #x0)] ;see above
        [count-encoded (cli-compress-unsigned (length param-list))]
        [ret-encoded
         ;see above
         (cond
           [(equal? 'void ret-type) (bytes #x1)]
           [else (encode-type-blob ret-type)])
         ]
        [param-encoded (if (empty? param-list) (bytes )  (reduce bytes-append (map encode-type-blob param-list)))]
        )
    (bytes-append by1 count-encoded ret-encoded param-encoded)))

(define (assemble-il-stream il-stream enc-lookup table-rid-lookup port)
  (for ([x il-stream])
    (match x
      [(list 'ret)
       (write-byte #x2A port)]
      [(list 'add)
       (write-byte #x58 port)]

      [(list 'ldc.i num)
       ; assume 32 bit for now
       (write-byte #x20 port)

       ; little endian?
       (write-byte (bitwise-and #xFF num) port)
       (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
       (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port)
       (write-byte (bitwise-and #xFF (arithmetic-shift num -24)) port)]
      [(list 'call ret-type (list assembly type) name param-list)
       (define num (table-rid-lookup 'memberref `(,ret-type (,assembly ,type) ,name ,param-list)))
       ;(writeln (format "memberref row id for ~a is ~a" x num))
       (write-byte #x28 port)
       
       ;type has the full assembly qualifier, this is a methodref. (memberref 0A)
       (write-byte (bitwise-and #xFF num) port)
       (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
       (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port)
       ;memberref
       (write-byte #x0A port)

       
       ]
      ;;       [(list 'call ret-type type name param-list)
      ;;        (define num (table-rid-lookup 'methoddef `(,ret-type ,type ,name ,param-list)))
      ;;        
      ;;        (write-byte #x28 port)
      ;;        ; this could be a methoddef or methodspec; don't support spec yet
      ;;        ; so assume def
      ;;        (write-byte (bitwise-and #xFF num) port)
      ;;        (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
      ;;        (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port)
      ;;        ;method
      ;;        (write-byte #x06 port)
      ;; 
      ;;        ]
      
      [else (wlf "warning, skipping ~s in il stream" x)]
      )))
  


(define (assemble-md md enc-lookup table-rid-lookup port)
  ; assemble method to the heap, and set the index.
  ; for now we assume everything to be 'tiny' header
  ; unti we can prove the exe works with our simple hello world
  (define index (file-position port))
  ; the second byte of the header is the size of the code which we don't know
  ; until we have assembled it.

  ; we'll assemble in a new bs then append... maybe another approach later.
  (define il (open-output-bytes))
  (assemble-il-stream (meth-builder-il-stream md) enc-lookup table-rid-lookup il)
  (define bs (get-output-bytes il))

  (set-meth-builder-il-index! md index)

  ; first byte is "tiny x2" and the 6 bit size
  (write-byte (bitwise-ior #x2 (arithmetic-shift (bytes-length bs) 2 )) port)
  
  (for ([b bs])
    (write-byte b port))
  )


(define (write-le-2 num port)
  (write-byte (bitwise-and #xFF num) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port))

(define (write-le-3 num port)
  (write-byte (bitwise-and #xFF num) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port))

(define (write-le-4 num port)
  (write-byte (bitwise-and #xFF num) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -24)) port))

(define (write-le-8 num port)
  (write-byte (bitwise-and #xFF num) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -8)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -16)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -24)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -32)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -40)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -48)) port)
  (write-byte (bitwise-and #xFF (arithmetic-shift num -56)) port)
  )

(define (align-stream align-to port)
  (let ([m (modulo (file-position port) align-to)])
    (if (equal? m 0)
        (void)
        (for [(i (in-range (- align-to m )))] (write-byte 0 port)))))

(define (assemble asm)
  ; todo
  ; extract sets of things for heaps * strings, user strings, blobs.
  ; most things are now extracted during parse, but we need to resolve/compose
  ; blobs for the method signatures in member ref and method defs. can't do this
  ; until we have typedef/ref indexes..

  ; sort, place and encode top level table items and build lookups
  
  (let ([tr (hash-ref (asm-builder-refs asm) 'typeref)])
    (for([key (hash-keys tr)]
         [i (in-naturals)])
      ; set row number starting at 1
      (hash-set! tr key (add1 i))))

  (define td-index
    (for/hash ([cb (asm-builder-class-defs asm)]
               [i (in-naturals)])
      (values (class-builder-name cb) (add1 i))))

  ; now we neeed to encode the blobs and place them in the lookup at the same time.
  ; we can place the signature in the blob index, and place the actual index as the
  ; value in the mr hash and method builder list;
  (define blob-heap (open-output-bytes))
  (write-byte 0 blob-heap); first byte is always 0
  ; encoding->index
  (define blob-index (make-hash))
  ; index->encoding
  (define index-blob (make-hash))

  ; for both memrefs and method defs, we need an index that returns
  ; their row id in their respective metatadata tables for the il assembler.
  ; they can share the index since the keys are unique (refs include the assembly)  
  (define meth-row-lookup (make-hash))
 
  ; memrefs  
  (for ([mr (hash-keys (hash-ref (asm-builder-refs asm) 'memref))]
        [i (in-naturals)])
    
    (let ([index (file-position blob-heap)]
          [encoded (encode-mr-blob mr)])
      (if (hash-has-key? blob-index encoded)
          (begin
            (hash-set! (hash-ref (asm-builder-refs asm) 'memref) mr (cons (hash-ref blob-index encoded) (add1 i)))
            (hash-set! meth-row-lookup mr (add1 i))
            )
          (begin
            (hash-set! blob-index encoded index)
            (hash-set! index-blob index encoded)
            (hash-set! (hash-ref (asm-builder-refs asm) 'memref) mr (cons index (add1 i)))
            (hash-set! meth-row-lookup mr (add1 i))
            ; first byte is blob len
            (write-byte (bytes-length encoded) blob-heap)
            (for ([b encoded])
              (begin
                ;(wlf "bh ~a" b)
                (write-byte b blob-heap)))
            ))))

  ; methoddefs
  ; the method defs are keyed by name iside a hash in the cb of their parent.
  ; the signature is identified by name, ret-type and the params - it is possible
  ; for methods from different types to share the sig.  set the waiting sig-index
  ; on each meth-builder
  ; TODO: this is not good enough - the typeref table needs to point at the first index
  ;  in the method table where its methods begin.  here we assign the indexes probably in some random
  ;  order due to the hash.  we need to do this more ordered and also store the index to the first method
  ;  on the cb.
  (for ([mb  (collect (map hash-values (map class-builder-meth-builders (asm-builder-class-defs asm))))]
        [table-index (in-naturals)])
    (let ([index (file-position blob-heap)]
          [encoded (encode-md-blob mb)])
      (if (hash-has-key? blob-index encoded)
          (begin
            (set-meth-builder-sig-index! mb (hash-ref blob-index encoded))
            (set-meth-builder-table-index! mb (add1 table-index))
            (hash-set! meth-row-lookup (mb->key mb) (add1 table-index)))          
          (begin
            (hash-set! blob-index encoded index)
            (hash-set! index-blob index encoded)
            (set-meth-builder-sig-index! mb index)
            (set-meth-builder-table-index! mb (add1 table-index))
            (hash-set! meth-row-lookup (mb->key mb) (add1 table-index))
            (write-byte (bytes-length encoded) blob-heap)
            (for ([b encoded]) (write-byte b blob-heap))))))



  ; finish blob heap
  (align-stream 4 blob-heap)
  (define blob-heap-size (file-position blob-heap))

  
  (define string-heap (open-output-bytes))
  (write-byte 0 string-heap); first byte is always 0
  ; string->offset lookup used when writing metadata tables
  (define string-index
    (for/hash ([s (hash-keys (hash-ref (asm-builder-refs asm) 'string))])
      
      (let([index (file-position string-heap)])
        ; (writeln s)
        (for ([b (string->bytes/latin-1 s)])
          (write-byte b string-heap))
        (write-byte 0 string-heap)
        (values s index)
        )))
  ; we know the heap will be placed at a 4-byte aligned address, so we can calculate
  ; any padding here to ensure it ends correctly aligned
  (writeln (get-output-bytes string-heap))
  (align-stream 4 string-heap)
  (define string-heap-size (file-position string-heap))
  (writeln (get-output-bytes string-heap))
  (writeln string-heap-size)
  
  

  ; the US heap will be empty to start with. for some reason it always has a 1 char blank string (a space)
  ; in additon to the null byte. all strings have a terminal byte to indicate unicode stuff, and
  ; each char is 2 bytes (16bit wide unicode) so even the 1 char string is 3 bytes
  (define us-heap (open-output-bytes))
  (write-bytes (bytes 0 3 #x32 0 0) us-heap)
  (align-stream 4 us-heap)
  (define us-heap-size (file-position us-heap))

  ; the guid heap is basically unused, there's always 1 in there for the module which we'll hardcode directly
  ; todo: generate a guid
  (define guid-heap (open-output-bytes))
  (write-bytes (bytes #xD8 #x7D #xD4 #x05 #xDD #xB2 #x70 #x4E #x98 #x35 #x01 #xC9 #x1E #x98 #x66 #x18) guid-heap)
  (align-stream 4 guid-heap)
  (define guid-heap-size (file-position guid-heap))
  (wlf "guid ~x" guid-heap-size)
  
  ;(writeln (collect (map hash-values (map class-builder-meth-builders (asm-builder-class-defs asm)))))
  ;;   (writeln blob-index)    
  ;;   (writeln index-blob)
  
  ; determine metadata token sizes

  ; we now know the size for the string and blob pointers
  (define ss (if (<= (file-position string-heap) #xFFFF) 2 4))
  (define bs (if (<= (file-position blob-heap) #xFFFF) 2 4))
  (define gs 2)

  (define (write-sr num port)
    (if (equal? ss 2) (write-le-2 num port) (write-le-4 num port)))
  (define (write-br num port)
    (if (equal? ss 2) (write-le-2 num port) (write-le-4 num port)))
  (define (write-gr num port)
    (write-le-2 num port))
  
  ; calculate each table's row count and size
  ; first pass we can't do the size since we need all the rows available
  (define tables
    (make-hash
     `(   [module ,@(table-data 'module 1 #x0  0)]
          [typeref ,@(table-data 'typeref 1 #x1  0)]
          [typedef ,@(table-data 'typedef 1 #x2  0)]
          [field ,@(table-data 'field 0 #x4  0)]
          [methoddef ,@(table-data 'methoddef 1 #x6  0)]
          [param ,@(table-data 'param 0 #x8  0)]
          [interfaceimpl ,@(table-data 'interfaceimpl 0 #x9  0)]
          [memberref ,@(table-data 'memberref 1 #xA  0)]
          [constant ,@(table-data 'constant 0 #xB  0)]
          [customattribute ,@(table-data 'customattribute 0 #xC  0)]
          [fieldmarshal ,@(table-data 'fieldmarshal 0 #xD  0)]
          [declsecurity ,@(table-data 'declsecurity 0 #xE  0)]
          [classlayout ,@(table-data 'classlayout 0 #xF  0)]
          [fieldlayout ,@(table-data 'fieldlayout 0 #x10  0)]
          [standalonesig ,@(table-data 'standalonesig 0 #x11  0)]
          [eventmap ,@(table-data 'eventmap 0 #x12  0)]
          [event ,@(table-data 'event 0 #x14  0)]
          [propertymap ,@(table-data 'propertymap 0 #x15  0)]
          [property ,@(table-data 'property 0 #x17  0)]
          [methodsemantics ,@(table-data 'methodsemantics 0 #x18  0)]
          [methodimpl ,@(table-data 'methodimpl 0 #x19  0)]
          [moduleref ,@(table-data 'moduleref 0 #x1A  0)]
          [typespec ,@(table-data 'typespec 0 #x1B  0)]
          [implmap ,@(table-data 'implmap 0 #x1C  0)]
          [fieldrva ,@(table-data 'fieldrva 0 #x1D  0)]                       
          [assembly ,@(table-data 'assembly 1 #x20  0)]
          [assemblyref ,@(table-data 'assemblyref 1 #x23  0)]
          [file ,@(table-data 'file 0 #x26  0)]
          [exportedtype ,@(table-data 'exportedtype 0 #x27  0)]
          [manifestresource ,@(table-data 'manifestresource 0 #x28  0)]
          [nestedclass ,@(table-data 'nestedclass 0 #x29  0)]
          [genericparam ,@(table-data 'genericparam 0 #x2A  0)]
          [methodspec ,@(table-data 'methodspec 0 #x2B  0)]
          [genericparamconstraint ,@(table-data 'genericparamconstraint 0 #x2C  0)])))

  ; now we can calculate the encodings
  (define encodings (make-hash))
  ; first is the simple table encoding, row counts into 2 of 4 bytes
  (for ([td (hash-values tables)])
    (hash-set! encodings (table-data-type td) (if (<= (table-data-row-count td) #xFFFF ) 2 4)))
  ; now the custom encodings
  (define (max-rows-lookup to-search)
    (for/fold ([max 0])
              ([table to-search])
      (let ([rows  (table-data-row-count (hash-ref tables table))])
        (if (> rows max) rows max))))
 
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
                        ;permission dunno what this is??
                        property event standalonesig moduleref typespec assembly
                        assemblyref file exportedtype manifestresource genericparam
                        genericparamconstraint methodspec))
           #x7FF) 2 4)) ; 5 bits

  ; we'll stick the heap sizes in as well for the assembler
  (hash-set! encodings 'ss ss)
  (hash-set! encodings 'bs bs)
  
  ; second pass of the tables to determine row size
  (define (calc-size items)
    (apply
     +
     (map (λ (x)
            (if (symbol? x)
                (if (hash-has-key? encodings x)
                    (hash-ref encodings x)
                    (begin
                      ; this can happen when the table doesn't exist
                      (writeln (format "warning, type ~a not found" x))
                      2))
                x)) items)))
  (for ([td (hash-values tables)])
    (set-table-data-row-size!
     td
     (calc-size
      (case (table-data-type td)
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
        [else (begin (writeln (format "warning: unknown type ~a in calc-size" (table-data-type td))) '(2))]))))
           
  (define total-tables-size
    (apply + (map (λ (td) (* (table-data-row-count td) (table-data-row-size td))) (hash-values tables))))

  (define total-~-stream-size
    ; the header for the ~ stream is 24 + (4 * num-tables) bytes
    ; then is is for some reason algined to xC. I don't thin this is needed
    ; but we'll put it in for now anyway.
    ;hardcoded for now
    (+ total-tables-size 24 28 4))
  
  (wlf "total table size : 0x~x" total-tables-size)
  (wlf "total ~~ size : 0x~x" total-~-stream-size)
  ; assemble IL and determine IL stream size and build offest
  ; for now we'll output all with 'fat' headers.  we can't calculate the rva yet,
  ; but we can asssemble and store our local relative offset into the il heap.
  ; then once we determine the section layout, we can re-calculate the actual rva
  ; when we are writing the metadata tables that reference the code.
  (define il-heap (open-output-bytes))
  
  
  ; the il will also need to know which row id some things appear at eg method, type, methodref, etc

  (define (table-rid-lookup type key)
    (case type
      ['memberref (hash-ref meth-row-lookup key)]
      ['methoddef (hash-ref meth-row-lookup key)]
      [else (raise (format "unsupported key in table-rid-lookup ~a : ~a" type key))]))
  
  (for ([md  (collect (map hash-values (map class-builder-meth-builders (asm-builder-class-defs asm))))])
    (assemble-md md encodings table-rid-lookup il-heap))

  (align-stream 4 il-heap)
  (define il-bytes (get-output-bytes il-heap))
  (define il-heap-size (bytes-length il-bytes))
  
  ;(writeln tables)
  ; ////////////////////////////////////////////////////////////////
  ; ////////////////////////////////////////////////////////////////

  ; time to write the executable.
  ; to start with we'll hardcode some locations and sizes
  ; we want to produce an identical file to nano2.exe.
  ; then, once working we'll gradually introduce each calculation
  ; and layout
  (define pe (open-output-file "c:\\temp\\rangi.exe" #:exists 'replace))
  

  ; before we can write the exe we need to determine the size of the .text section
  ; which contains the cli metadata and il opcodes.
  ; we know our .text can always start at x2000 so that makes it slightly easier
  ; the structure is as follows
  ; 0x2000 .text
  ; (x8) import adress table. this is an rva into the hint/name table after the cli data. and an empty 4 bytes.
  ; (x48) cli header (includes pointer to metadata, after il )
  ; n  il bytes (align 4)
  ; metadata header / root
  ; metadata
  ; import table 
  ; import lookup table
  ; hint/name table

  ; it is critical that the hint/name table is folllowed by the FF 25 bytes and then the entrypoint rva.
  ; (this FF 25 is pointed at by the EntrypointRva in the PE header).  The actual RVA following the 2 bytes
  ; must appear at the start of a 32 bit boundary, so we have to pad after the hint/name table so that the
  ; FF 25 bytes appear at the end of the previous boundary;  all this means the final size of the section
  ; has to be calculated with this in mind. 

  ; so first we can calculcate all the cli bits since we know the sizes of all that
  (define cli-segment-size
    (+
     #x8   ; IAT
     #x48  ; cli header
     il-heap-size  ; il code (aligned)
     #x20  ; metadata root
     #x4C  ; metadata headers.  this is known ahead of time since there's always the same 5 streams
     total-~-stream-size ; includes header
     string-heap-size
     us-heap-size
     guid-heap-size
     blob-heap-size
     #x28  ; import descriptor
     #x8   ; lookup
     ))

    
  (define cli-to-hint-size
    (+
     (if (equal? (modulo cli-segment-size 16) 0)
         0
         (- 16 (modulo cli-segment-size 16)))))

  
  (wlf "il ~x" il-heap-size)
  (wlf "~~ ~x" total-~-stream-size)
  (wlf "strings ~x" string-heap-size)
  (wlf "us ~x" us-heap-size)
  (wlf "guid ~x" guid-heap-size)
  (wlf "blob ~x" blob-heap-size)
  (wlf "cli seg ~x" cli-segment-size)
  (wlf "cli to hint ~x" cli-to-hint-size)
  
  (define import-size #x30)
  
  ; and we also know that the cli segment starts at a 32 bit aligned address
  (define text-section-size
    (+
     cli-segment-size
     cli-to-hint-size
     import-size
     ))


  
  (wlf ".text section size x~x ~a" text-section-size text-section-size)
  (when (>= text-section-size #x400 )
    (raise ".text section larger than x400.  Now you'll have to do that work you've been putting off!"))
  
  ; calculate section sizes and determine layout
  (define text-section-phys #x200)
  (define text-section-virt #x2000)
  (define reloc-section-phys #x600)
  (define reloc-section-virt #x4000)

  ; the "import-lookup-start-phys" is the location after the cli, intial import table and padding.
  ; this is where the hint table starts.
  (define import-hint-start-phys (+ text-section-phys cli-segment-size cli-to-hint-size))
  (wlf "hint start x~x " import-hint-start-phys)
  
  (define (calc-text-rva offset)
    (+ text-section-virt offset))

  ; start of the import table directly afer the blob heap
  (define import-start-offset (- cli-segment-size #x30))
  (define import-start-rva (calc-text-rva import-start-offset))

;  (define dll-hint-rva (calc-text-rva (- (+ import-lookup-start-phys #x1F) text-section-phys)))
  
  ; this is the address that appears as the first item in the import table, pointing to the
  ; lookup table below it
  (define import-table-rva-to-lookup (calc-text-rva (- (+ text-section-phys import-start-offset #x28) text-section-phys)))

  (define dll-hint-rva (+ import-table-rva-to-lookup #x8 ))
  (define dll-name-rva (+ dll-hint-rva #xE))
  ; points past the hint table 
  (define entry-point-rva (+ dll-hint-rva #x1E ))
  
  (wlf "import start rva ~x" import-start-rva)
  (wlf "import table rva to lookup  ~x" import-table-rva-to-lookup)
  (wlf "entrypoint  ~x" entry-point-rva)

  ;(wlf "dll off  ~x" (calc-text-rva (- (+ import-start-phys #x38) text-section-phys)))
  (wlf "dll hint ~x" dll-hint-rva)
  ; write PE -

  ;   ms dos header
  (write-bytes (bytes #x4D #x5A #x90 #x00 #x03 #x00 #x00 #x00 #x04 #x00 #x00 #x00 #xFF #xFF #x00 #x00 #xB8 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x40 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x80 #x00 #x00 #x00 #x0E #x1F #xBA #x0E #x00 #xB4 #x09 #xCD #x21 #xB8 #x01 #x4C #xCD #x21 #x54 #x68 #x69 #x73 #x20 #x70 #x72 #x6F #x67 #x72 #x61 #x6D #x20 #x63 #x61 #x6E #x6E #x6F #x74 #x20 #x62 #x65 #x20 #x72 #x75 #x6E #x20 #x69 #x6E #x20 #x44 #x4F #x53 #x20 #x6D #x6F #x64 #x65 #x2E #x0D #x0D #x0A #x24 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x50 #x45 #x00 #x00)
               pe)

  ; pe fiel header. pg 305
  ; note the number of sections and opt header size are in here
  ; also the characteristics flag determines exe / dll
  (write-bytes (bytes #x4C #x01 #x02 #x00 #x0C #xFF #x44 #x68 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xE0 #x00 #x02 #x01)
               pe)

  ; pe header
  ; 28 bytes standard fields
  ; 68 bytes nt 
  ; 128 bytes data directories
  ; a lot of important data in here that needs calculating, including the section sizes, entry point rva, base of code / data
  
  ; standard
  #;(write-bytes (bytes #x0B #x01 #x0B #x00 #x00 #x04 #x00 #x00 #x00 #x02 #x00 #x00 #x00 #x00 #x00 #x00 #x1E #x22 #x00 #x00 #x00 #x20 #x00 #x00 #x00 #x40 #x00 #x00)
                 pe)
  (write-le-2 #x10B pe) ;magic
  (write-byte 6 pe)     ; l major always 6 
  (write-byte 5 pe)     ; l minor always 5
  (write-le-4 #x400 pe)    ; code size TODO: we already calculate the .text size but need to work on various areas when it grows beyond
  (write-le-4 #x200 pe)    ; data size (no data yet)
  (write-le-4 #x0 pe)    ; uninitdata size (no data yet)
  (write-le-4 entry-point-rva pe)
  (write-le-4 #x2000 pe)  ; code rva TODO: when this moves...
  (write-le-4 #x4000 pe)  ; data rva TODO: when this moves...
  
  
  ; nt
  (write-bytes (bytes #x00 #x00 #x40 #x00 #x00 #x20 #x00 #x00 #x00 #x02 #x00 #x00 #x04 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x04 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x60 #x00 #x00 #x00 #x02 #x00 #x00 #x00 #x00 #x00 #x00 #x03 #x00 #x40 #x85 #x00 #x00 #x10 #x00 #x00 #x10 #x00 #x00 #x00 #x00 #x10 #x00 #x00 #x10 #x00 #x00 #x00 #x00 #x00 #x00 #x10 #x00 #x00 #x00 )
               pe)
  

  ;data dirs
  ; this includes the all important cli-header pointer
  #;(write-bytes (bytes #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #xC8 #x21 #x00 #x00 #x53 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x40 #x00 #x00 #x0C #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x20 #x00 #x00 #x08 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x08 #x20 #x00 #x00 #x48 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 )
                 pe)
  (write-le-8 0 pe)   ; Export

  (write-le-4 import-start-rva pe)   ; Import rva
  (write-le-4 #x53 pe)   ; import size alwyas same
  
  (write-le-8 0 pe)   ; resoruce
  (write-le-8 0 pe)   ; exception
  (write-le-8 0 pe)   ; security
  
  (write-le-4 #x4000 pe)   ; reloc rva
  (write-le-4 #xC pe)   ; reloc size always same

  (write-le-8 0 pe)   ; debug
  (write-le-8 0 pe)   ; copyright
  (write-le-8 0 pe)   ; globalptr
  (write-le-8 0 pe)   ; tls
  (write-le-8 0 pe)   ; loadconfig
  (write-le-8 0 pe)   ; boundimport

  (write-le-4 #x2000 pe)   ; iat rva
  (write-le-4 #x8 pe)   ; always same size

  
  (write-le-8 0 pe)   ; delayload

  (write-le-4 #x2008 pe)   ; clr rva
  (write-le-4 #x48 pe)   ; header always same size
  
  (write-le-8 0 pe)   ; reserved
  
  ; next are the section headers, this exe has 2 sections .text and .reloc
  ; each header is 40 bytes
  ;.text
  (write-bytes (bytes #x2E #x74 #x65 #x78 #x74 #x00 #x00 #x00 #x24 #x02 #x00 #x00 #x00 #x20 #x00 #x00 #x00 #x04 #x00 #x00 #x00 #x02 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x20 #x00 #x00 #x60 )
               pe)

  ;.reloc
  (write-bytes (bytes #x2E #x72 #x65 #x6C #x6F #x63 #x00 #x00 #x0C #x00 #x00 #x00 #x00 #x40 #x00 #x00 #x00 #x02 #x00 #x00 #x00 #x06 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x40 #x00 #x00 #x42 )
               pe)

  ; now we pad until 200
  (for ([i (in-range (- #x200 (file-position pe)))])
    (write-byte 0 pe))

  ; iat table #x200
  ; this is the rva to the dll in the hint/name table
  (write-le-4 dll-hint-rva pe)
  (write-le-4 0 pe)
  
  ;cli header : #x208
  ; this has some very important things to calculate, including the size of the metadata and entrypoint token
  
  (write-le-4 #x48 pe)  ; header size
  (write-le-2 2 pe)     ; major
  (write-le-2 0 pe)     ; minor
  (write-le-4 (calc-text-rva (+ #x48 #x8 il-heap-size)) pe) ;rva for metadata - this is from the start of the section, skipping iat, cli header and il
  (write-le-4
   (+  #x6C  ; metadata headers.  this is known ahead of time since there's always the same 5 streams
       total-~-stream-size ; includes header
       string-heap-size
       us-heap-size
       guid-heap-size
       blob-heap-size ) pe )  ; metadata size

  ; rest is hardcoded : todo, output entrypoint token
  (write-bytes (bytes #x01 #x00 #x00 #x00 #x01 #x00 #x00 #x06 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 )
               pe)
  

  
  ;at x250 we output our il
  (define il-start-offset (file-position pe))
  (wlf "il start ~x" (file-position pe))
  (for ([b il-bytes])
    (write-byte b pe))

  ; at x25C we begin the actual cli metadata
  ; magic sig
  (define cli-root (file-position pe))
  (write-le-4 #x424A5342 pe)
  ; major
  (write-le-2 #x1 pe)  
  ; minor
  (write-le-2 #x1 pe)
  ; reserved
  (write-le-4 #x0 pe)
  ; todo: there is a bit of messing around calcutiong the size of, and encdoing
  ;  the version number.  we'll just hardcode Length and Version
  (write-bytes (bytes #x0C #x00 #x00 #x00 #x76 #x34 #x2E #x30 #x2E #x33 #x30 #x33 #x31 #x39 #x00 #x00 )
               pe)
  ; flags (always 0)
  (write-le-2 #x0 pe)

  ; number of streams (always 5? sice we write the US blob even if its empty)
  (write-le-2 #x5 pe)
  (define stream-header-start (file-position pe))
  (define stream-header-offset (- stream-header-start cli-root))
  
  ; x27C
  ; now follows each stream header.  we need to calculate:
  ;  offset 4  - start of stream from meta root
  ;  size 4 - size of stream, multiple of 4 (althogh it says 4, it seems the assembler aligns the result end position to 8)
  ;  name - limit 32 chars padded to 4byte boundary. in practice there are only 5 names. #~, #String, #US, #Blob, #Guid

  ; the size of these headers is varaible due to the name, but in practice we know they will start algined so we already know
  ; any padding they will need, and so the total size of all headers is known
  (define total-stream-header-size #x4C)
  (define stream-~-offset (+ stream-header-offset total-stream-header-size))
  (define stream-strings-offset (+ stream-~-offset total-~-stream-size))
  (define stream-us-offset (+ stream-strings-offset string-heap-size))
  (define stream-guid-offset (+ stream-us-offset us-heap-size))
  (define stream-blob-offset (+ stream-guid-offset guid-heap-size))

  ; write headers
  ; ~
  (write-le-4 stream-~-offset pe)
  (write-le-4 total-~-stream-size pe)
  (write-bytes (bytes #x23 #x7E #x00 #x00) pe) ; #~
  
  (write-le-4 stream-strings-offset pe)
  (write-le-4 string-heap-size pe)
  (write-bytes (bytes #x23 #x53 #x74 #x72 #x69 #x6E #x67 #x73 #x00 #x00 #x00 #x00 ) pe) ; #Strings
  
  (write-le-4 stream-us-offset pe)
  (write-le-4 us-heap-size pe)
  (write-bytes (bytes #x23 #x55 #x53 #x00 ) pe) ; #US
  
  (write-le-4 stream-guid-offset pe)
  (write-le-4 guid-heap-size pe)
  (write-bytes (bytes #x23 #x47 #x55 #x49 #x44 #x00 #x00 #x00 ) pe) ; #GUID
  
  (write-le-4 stream-blob-offset pe)
  (write-le-4 blob-heap-size pe)
  (write-bytes (bytes #x23 #x42 #x6C #x6F #x62 #x00 #x00 #x00  ) pe) ; #Blob

  (wlf "stream #~~ location ~x" (file-position pe))
  ; ///////////////////////////////////////////////////////////////////////////
  ; BEGIN #~ STREAM
  ;
  (write-le-4 0 pe)     ; Reserved, always 0
  (write-byte 2 pe)     ; Major, always 2
  (write-byte 0 pe)     ; Minor, always 0
  ; todo: heap sizes, 0 for now since they are 2 bytes in our example
  (write-byte 0 pe)     ; Heap sizes: todo, bottom 3 bits determine it strings, guid, blob are 4 bytes
  (write-byte 1 pe)     ; Reserved, always 1
  ; todo: valed, hardcoded for the 7 tables present in the example
  (write-le-8 #x0900000447 pe)     ; Valid.  bit vector showing which tables are present
  ; todo: sorted. the spec is unlear on this. hardcoding it for now
  ; and need to experiment with ths later  
  (write-le-8 #x16003325FA00 pe)     ; Sorted.  not sure what this is
  ; next is the 4-byte length of each table
  ; we have the info to do this but hardcode them to 1 for now
  (for ([i (in-range 7)]) (write-le-4 1 pe))
  ; and now we have the table rows laid out in order.

  
  ; we are semi-hardcoding this for now

  ; first is module 0x0
  (wlf "module start ~x" (file-position pe))
  (write-bytes (bytes 0 0) pe)  ;generation, always 0
  (write-sr (hash-ref string-index (symbol->string(asm-builder-mod-def asm))) pe) ; name
  (write-gr 1 pe)  ;mvid guid ref
  (write-gr 0 pe)  ;encid, always 0 guid ref
  (write-gr 0 pe)  ;encbaseid, always 0 guid ref
  
  (wlf "typeref start ~x" (file-position pe))
  ;(wlf "~a" (hash-ref (asm-builder-refs asm) 'typeref))
  ;(wlf "~a" (sort (hash->list (hash-ref (asm-builder-refs asm) 'typeref)) < #:key cdr))
  ; a typedef has a resolutionscope tag, there are exotic uses, but for now
  ; all our typerefs will be of type assemblyref (type in external asm)
  ; TODO: like the tr index, we need a ar index which gives the row layout of
  ; assemblyref table.  for now we only have 1 so we'll just hardcode it
  (for ([pair (sort (hash->list (hash-ref (asm-builder-refs asm) 'typeref)) < #:key cdr)])
    (match pair
      [(cons (list asm type) index)
       (wlf "~a" type)
       (let ([split (string-split (symbol->string type) ".")])
         ;(wlf "~a" (hash-ref string-index (car split)))
         ;(wlf "~a" (hash-ref string-index (cadr split)))
         ; first is resolution scope, lowest 2 bits are 10 (assemblyref)
         ; TODO: lookup and use correct size for 'resolutionscope
         
         ; todo: lookup assembly ref row index
         (write-le-2 (bitwise-ior #x2 (arithmetic-shift #x1 2))  pe)
         ; note: these two seem to be around the wrong way in the spec!!!
         (write-sr (hash-ref string-index (cadr split)) pe)  ;namespace 
         (write-sr (hash-ref string-index (car split)) pe)  ;type name
         )
       ]
      [else (raise "unexpected typeref")]))

  (wlf "typedef start ~x" (file-position pe))
  (for ([cb (asm-builder-class-defs asm)])
    ;    (wlf "~a" cb)
    (write-le-4 0 pe)  ; flags TODO, we are not encoding these yet, they are zero for our type 
    (write-sr (hash-ref string-index (symbol->string (class-builder-name cb))) pe) ; name
    (write-sr 0 pe)  ;namespace
    ; 'typedeforref  typedef extends.  module pseudo-classextends itself seemingly
    (write-le-2 0  pe)         

    (write-le-2 1  pe) ; fieldlist - field index todo: proper size

    (write-le-2 1  pe) ; methodlist - field index todo: proper size
    
    
    )
                                          
  (wlf "method start ~x" (file-position pe))
  (for ([cb (asm-builder-class-defs asm)])
    (for ([mb (sort (hash-values (class-builder-meth-builders cb)) < #:key meth-builder-table-index)])
      ; first field is the RVA. This will be the virt section address + (il start offset - physical offset of section start) + il index
      (write-le-4 (+ #x2000 (- il-start-offset #x200) (meth-builder-il-index mb)) pe)
      (write-le-2 0 pe)  ; implflags todo
      (write-le-2 #x16 pe)  ; flags todo
      (write-sr (hash-ref string-index (symbol->string (meth-builder-name mb))) pe)  ; name
      (write-br (meth-builder-sig-index mb) pe)  ; signature
      (write-le-2 1 pe)  ; paramlist todo
      
      
      ;    (wlf "~a" mb)
      )
    )

  (wlf "memberref start ~x" (file-position pe))
  (for ([mb (sort (hash->list (hash-ref (asm-builder-refs asm) 'memref)) < #:key caddr)])
    (wlf "~a" mb)
    (wlf "~a" (cdar mb))
    
    (match (car mb)
      [(list ret (list asm type) name params)
       ; class - memberrefparent - for us this is only typedef at the moment
       ; 3 bits, zero
       ; todo: lookup typeref index
       (write-le-2 (bitwise-ior #x1 (arithmetic-shift #x1 3))  pe)
       (write-sr (hash-ref string-index (symbol->string name)) pe) ; name
       (write-br (car (cdr mb)) pe) ; signature

       ]
      [else (raise "!")])
    
    )
  ; 
  (wlf "assembly start ~x" (file-position pe))
  (write-le-4 0 pe)  ;hashalgid
  (write-le-8 0 pe)  ;major, minor, build, rev
  (write-le-4 0 pe)  ;flags
  (write-br 0 pe)  ;public key
  (write-sr (hash-ref string-index (symbol->string (asm-builder-asm-def asm))) pe)  ;public key
  (write-sr 0 pe)

  (wlf "assemblyref start ~x" (file-position pe))
  (write-le-8 0 pe)  ;major, minor, build, rev
  (write-le-4 0 pe)  ;flags
  (write-br 0 pe)  ;public key
  (write-sr (hash-ref string-index "mscorlib") pe)  ;public key  
  (write-sr 0 pe)

  ;mysterious padding bytes
  (write-le-4 0 pe)
  (write-le-2 0 pe)

  
  ; END #~ STREAM
  ; ////////////////////////////////////////////////////////////////////////////
  
  
  ; ////////////////////////////////////////////////////////////////////////////
  ; begin #Strings stream
  (wlf "strings start ~x" (file-position pe))
  (write-bytes (get-output-bytes string-heap) pe)
  

  ; ////////////////////////////////////////////////////////////////////////////
  ; begin #Us stream
  (wlf "us start ~x" (file-position pe))
  (write-bytes (get-output-bytes us-heap) pe)


  ; ////////////////////////////////////////////////////////////////////////////
  ; begin #guid stream
  (wlf "guid start ~x" (file-position pe))
  (write-bytes (get-output-bytes guid-heap) pe)


  ; ////////////////////////////////////////////////////////////////////////////
  ; begin #blob stream
  (wlf "blob start ~x" (file-position pe))
  (write-bytes (get-output-bytes blob-heap) pe)
  
  
  ;;   (define (bytes-to-next n align)
  ;;    (if (equal? (modulo n align) 0)
  ;;        0
  ;;        (- align (modulo n align))))

  
  ;"import table : 3c8"  this is pointed to by the rva in the  "import" section header
  ; 31 bit rva into the "hint/name" table (which is the actual table...)
  (define import-start (file-position pe))
  
  (wlf "import start ~x" (file-position pe))
  (wlf "import start ~x" import-table-rva-to-lookup)


  (write-le-4 import-table-rva-to-lookup pe)  ; pointer to lookup table
  (write-le-4 0 pe)   ; datestamp
  (write-le-4 0 pe)   ; fwd chain
  (write-le-4 dll-name-rva pe)   ; name rva
  (write-le-4 #x2000 pe)   ; iat
  ;some padding
  (write-le-4 0 pe)
  (write-le-8 0 pe)
  (write-le-8 0 pe)

  
  ; now the import lookup table, it's the same as the iat before the cli metadata header
  (write-le-4 dll-hint-rva pe)
  (write-le-4 0 pe)
  ; except some more padding
;  (write-le-8 0 pe)
  ; now the hint/name table, dll string and actual entry point bits  
  (write-bytes (bytes   #x00 #x00 #x5F #x43 #x6F #x72 #x45 #x78
                        #x65 #x4D #x61 #x69 #x6E #x00 #x6D #x73 #x63 #x6F #x72 #x65 #x65 #x2E #x64 #x6C
                        #x6C #x00 #x00 #x00 #x00 #x00 ) pe)

  ; before we write the FF 25 and the rva, we need to align so that the rva
  ; will start on a 16 bit boundary
  ;(align-stream 31 pe)
  (write-byte #xFF pe)
  (write-byte #x25 pe)
  (define entry-point-physical (file-position pe))
  
  (write-le-4 #x402000 pe)  ; rva of reloc firs byte TODO this will need changing when the size of .text changes
  
  (do ()
    ((equal? (file-position pe) #x600))
    (write-byte 0 pe))
  ;"base reloc table : 600"

  (write-le-4 #x2000 pe)  ; page rva
  (write-le-4 #xC pe)  ; block size
  ; the offest to patch is the one that appaers after the FF 25 bytes at the end of the name table.
  ; at tho moment we calculate thi backwards from the algined size of the text section, this will do for now
  ; until we support different sized sections.
  ; top 4 bits are x3 for IMAGE_REL_BASED_HIGHLOW
  ; other 12 bits are the offest from the text start
  ;(write-le-2 (bitwise-ior (arithmetic-shift 3 12) (- (+ entry-point-rva 2) text-section-virt)) pe)
  
  (write-le-2 (bitwise-ior (arithmetic-shift 3 12) (- text-section-size #x10)) pe)
  ;(write-bytes (bytes #x00 #x20 #x00 #x00 #x0C #x00 #x00 #x00 #x20 #x32 #x00 #x00 #x00 #x00 #x00 #x00 ) pe)
  (do ()
    ((equal? (file-position pe) #x800))
    (write-byte 0 pe))
  (writeln (file-position pe))
  ;   pe & opt header
  ;   sections .text
  ;     cli metadata root
  ;     metadata stream headers
  ;     heaps
  ;     metadata tables
  ;     IL

  (close-output-port pe)
  #f
  )
(time (assemble (parse-il nano2)))

 





