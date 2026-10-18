#lang racket/base
; Portable PDB writer (PortablePdb-Metadata.md). build-pdb turns the method debug data of a module
; into the PDB file: a metadata root with the #Pdb, #~, #Strings, #US, #GUID and #Blob streams.
; The output depends only on its input. The PDB Id is a SHA-1 of the file with the Id zeroed, so
; it is not a GUID or a timestamp.
(require racket/list
         "../cli/tables.rkt"
         "../cli/schema.rkt"
         "../cli/heaps.rkt"
         "../cli/sigs.rkt"
         "../cli/metadata.rkt"
         "../private/binary.rkt"
         "model.rkt")
(provide (struct-out pdb-image)
         build-pdb)

; bytes: the whole file, with the Id in place. id: the 20-byte PDB Id. checksum: the SHA-256 of
; the file with the Id zeroed, which the PdbChecksum debug entry records.
(struct pdb-image (bytes id checksum))

; The CLI tables the PDB refers to (#Pdb ReferencedTypeSystemTables). They are counted, not held:
; MethodDef for LocalScope and StandAloneSig for the LocalSignature rids.
(define referenced-methoddef #x06)
(define referenced-standalonesig #x11)

; methods: one entry per MethodDef row, in rid order, each a methoddebug or #f for a body-less method.
; entry-point: the MethodDef token of the entry point, or 0.
; standalone-sig-count: the StandAloneSig rows of the CLI, which the local signatures refer to.
(define (build-pdb methods #:entry-point entry-point #:standalone-sig-count sig-count)
  (define method-count (length methods))
  (define sh (make-strings-heap))
  (define uh (make-us-heap))
  (define gh (make-guid-heap))
  (define bh (make-blob-heap))
  (define tb (make-tables #:schema schema-pdb-tables))

  ; A Document row per distinct file, in order of first use. Its name is a document name blob
  ; (PortablePdb-Metadata.md): separator byte 0 (none), then one part, a #Blob index holding the UTF-8 name.
  (define doc-rids (make-hash))
  (define files
    (remove-duplicates
     (for*/list ([m (in-list methods)] #:when m [p (in-list (methoddebug-seqpts m))])
       (seqpt-file p))))
  (for ([f (in-list files)])
    (define part (heap-add! bh (string->bytes/utf-8 f)))
    (define name (heap-add! bh (bytes-append (bytes 0) (compress-unsigned part))))
    (hash-set! doc-rids f (add-row! tb 'document name 0 0 0)))

  ; MethodDebugInformation, one row per MethodDef. A method whose points are all in one file names
  ; that file. A method spanning several files names none and gives its first file as InitialDocument.
  (for ([m (in-list methods)])
    (cond
      [(or (not m) (null? (methoddebug-seqpts m)))
       (add-row! tb 'methoddebuginformation 0 0)]
      [else
       (define seqpts (methoddebug-seqpts m))
       (define first-doc (hash-ref doc-rids (seqpt-file (car seqpts))))
       (define multi? (> (length (remove-duplicates (map seqpt-file seqpts))) 1))
       (define blob
         (heap-add! bh (encode-sequence-points (methoddebug-locals-rid m) seqpts doc-rids
                                               (and multi? first-doc))))
       (add-row! tb 'methoddebuginformation (if multi? 0 first-doc) blob)]))

  ; One LocalScope per method with named locals, spanning the whole body, and its LocalVariable rows.
  ; ConstantList 1 is the first LocalConstant row of the run; there are no constants, so the run is empty.
  (for ([m (in-list methods)] [rid (in-naturals 1)]
        #:when (and m (pair? (methoddebug-local-names m))))
    (add-row! tb 'localscope rid 0 (add1 (table-row-count tb 'localvariable)) 1
              0 (methoddebug-code-size m))
    (for ([ln (in-list (methoddebug-local-names m))])
      (add-row! tb 'localvariable 0 (car ln) (heap-add! sh (cdr ln)))))

  (sort-tables! tb)
  (define strs (pad-to (heap-serialise sh) 4))
  (define us (pad-to (heap-serialise uh) 4))
  (define blobs (pad-to (heap-serialise bh) 4))
  (define-values (tilde no-rva-fixups)
    (tables-stream tb
                   #:string-wide? (> (bytes-length strs) #xFFFF)
                   #:blob-wide? (> (bytes-length blobs) #xFFFF)
                   #:guid-wide? #f
                   #:external-rows (lambda (name)
                                     (case name
                                       [(methoddef) method-count]
                                       [(standalonesig) sig-count]
                                       [else 0]))))
  (unless (null? no-rva-fixups)
    (error 'build-pdb "the PDB tables have no RVA cells"))

  ; #Pdb (PortablePdb-Metadata.md): the 20-byte Id, the entry point, the bit vector of referenced
  ; CLI tables, then one row count per set bit, in bit order.
  (define referenced
    (+ (arithmetic-shift 1 referenced-methoddef) (arithmetic-shift 1 referenced-standalonesig)))
  (define pdb-stream
    (bytes-append (make-bytes 20 0) (le entry-point 4) (le referenced 8)
                  (le method-count 4) (le sig-count 4)))

  (define-values (zeroed offsets)
    (metadata-bytes (list (cons "#Pdb" pdb-stream)
                          (cons "#~" tilde)
                          (cons "#Strings" strs)
                          (cons "#US" us)
                          (cons "#GUID" (heap-serialise gh))
                          (cons "#Blob" blobs))
                    #:version "PDB v1.0"))
  (define id (sha1-bytes zeroed))
  (define checksum (sha256-bytes zeroed))
  (define final (bytes-copy zeroed))
  (bytes-copy! final (car offsets) id)
  (pdb-image final id checksum))

; The sequence points blob (PortablePdb-Metadata.md, Sequence Points Blob): the LocalSignature rid,
; the InitialDocument when the method spans several documents, then one record per point. The first
; record has its IL offset and start position absolute; later ones are deltas. A document change is
; a record with a zero offset delta and the new document's rid.
(define (encode-sequence-points local-sig seqpts doc-rids initial-doc)
  (define (doc-of p) (hash-ref doc-rids (seqpt-file p)))
  (define header
    (bytes-append (compress-unsigned local-sig)
                  (if initial-doc (compress-unsigned initial-doc) #"")))
  (define body
    (let loop ([ps seqpts] [cur-doc (doc-of (car seqpts))] [prev #f] [acc '()])
      (cond
        [(null? ps) (apply bytes-append (reverse acc))]
        [else
         (define p (car ps))
         (define dl (- (seqpt-end-line p) (seqpt-start-line p)))
         (define dc (- (seqpt-end-col p) (seqpt-start-col p)))
         (when (or (negative? dl) (and (zero? dl) (<= dc 0)))
           (error 'build-pdb "sequence point at IL ~a ends before it starts" (seqpt-offset p)))
         (define d (doc-of p))
         (define doc-record
           (if (= d cur-doc) #"" (bytes-append (compress-unsigned 0) (compress-unsigned d))))
         (define record
           (bytes-append
            (compress-unsigned (if prev (- (seqpt-offset p) (seqpt-offset prev)) (seqpt-offset p)))
            (compress-unsigned dl)
            (if (zero? dl) (compress-unsigned dc) (compress-signed dc))
            (if prev
                (bytes-append (compress-signed (- (seqpt-start-line p) (seqpt-start-line prev)))
                              (compress-signed (- (seqpt-start-col p) (seqpt-start-col prev))))
                (bytes-append (compress-unsigned (seqpt-start-line p))
                              (compress-unsigned (seqpt-start-col p))))))
         (loop (cdr ps) d p (cons record (cons doc-record acc)))])))
  (bytes-append header body))
