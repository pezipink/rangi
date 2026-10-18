#lang racket/base
; Turns a #~ image into the same image with the uncompressed #- stream and HeapSizes flag 0x40.
; II.24.2.6 does not define the 4 bytes that 0x40 adds before the table rows. SRM reads them
; and ignores them (ReadMetadataTableHeader), so the decoded tables do not change.
; With #:pointer-tables, the named pointer tables (II.22 MethodPtr and friends) are added just
; before their target tables. Each one lists the target rows of every owner's run in reverse,
; so the indirection is not the identity and a reader that ignores it sees the wrong members.
; The metadata grows by delta bytes: the 4 extra bytes, one count per new table, and the new
; rows. Everything after the #~ stream moves by delta, so the patch also updates every stored
; RVA and file position past it: PE header fields, the CLI header, stream headers, MethodDef
; and FieldRVA rows, the import directory and base relocations. The delta bytes come from zero
; padding at the end of .text, so no raw size changes.
(require racket/port "../../src/cli-reader.rkt" "../../src/cli/schema.rkt")
(provide tilde->uncompressed)

; pointer table name -> owner table, owner's list column, target table (II.22.37, II.22.35, ...)
(define pointer-specs
  '((methodptr typedef method-list methoddef)
    (fieldptr typedef field-list field)
    (paramptr methoddef param-list param)
    (eventptr eventmap event-list event)
    (propertyptr propertymap property-list property)))

(struct section (va vsize rawsize rawptr hdr))

; a pointer table to add: its id, row count (the target table's rows), and row bytes
(struct ptr (name id target rows data))

(define (u16 b o) (integer-bytes->integer b #f #f o (+ o 2)))
(define (u32 b o) (integer-bytes->integer b #f #f o (+ o 4)))
(define (put-u16! b o v) (bytes-copy! b o (integer->integer-bytes v 2 #f #f)))
(define (put-u32! b o v) (bytes-copy! b o (integer->integer-bytes v 4 #f #f)))

; The rows of one pointer table. Position p of the pointer table holds the target rid that the
; owner row whose run contains p lists at that position. Each run is reversed, the other
; positions are the identity. The owners' list columns are left alone, so the owner rows stay
; the same (II.22.37 MethodList and friends).
(define (make-pointer rdr spec)
  (define-values (name owner list-col target) (apply values spec))
  (define n (table-row-count rdr target))
  (define w (if (> n #xFFFF) 4 2))
  (define perm (for/vector #:length n ([p (in-range 1 (add1 n))]) p))
  (define m (table-row-count rdr owner))
  (define starts
    (for/vector #:length m ([rid (in-range 1 (add1 m))])
      (row-column-raw rdr owner rid list-col)))
  (for ([i (in-range m)])
    (define s (vector-ref starts i))
    (define next (if (< (add1 i) m) (vector-ref starts (add1 i)) (add1 n)))
    (define e (min (add1 n) (max s next)))
    (for ([p (in-range (max s 1) e)])
      (vector-set! perm (sub1 p) (- (+ s e -1) p))))
  (ptr name
       (table-id (table-by-name name))
       target
       n
       (apply bytes-append
              (for/list ([v (in-vector perm)]) (integer->integer-bytes v w #f #f)))))

; path of a PE32 image with a #~ stream; returns the patched image as bytes.
; pointer-tables names the pointer tables (see pointer-specs) to add to the image.
(define (tilde->uncompressed path #:pointer-tables [pointer-tables '()])
  (for ([name (in-list pointer-tables)])
    (unless (assq name pointer-specs)
      (error 'tilde->uncompressed "unknown pointer table ~a" name)))
  (define orig (call-with-input-file path port->bytes))
  (define img (bytes-copy orig))
  (define rdr (read-file path))
  (define tables (asm-reader-table-attributes rdr))

  ; PE32 optional header fields (II.25.2.3)
  (define pe (u32 orig #x3C))
  (define opt (+ pe 24))
  (unless (= (u16 orig opt) #x10B)
    (error 'tilde->uncompressed "only PE32 images are supported"))
  (define image-base (u32 orig (+ opt 28)))
  (define entry-field (+ opt 16))
  (define dirs (+ opt 96))
  (define (dir-rva i) (u32 orig (+ dirs (* 8 i))))
  (define (dir-size i) (u32 orig (+ dirs (* 8 i) 4)))
  (define opt-size (u16 orig (+ pe 20)))
  (define sections
    (for/list ([i (in-range (u16 orig (+ pe 6)))])
      (define h (+ opt opt-size (* 40 i)))
      (section (u32 orig (+ h 12)) (u32 orig (+ h 8)) (u32 orig (+ h 16)) (u32 orig (+ h 20)) h)))
  (define (section-of rva)
    (or (for/first ([s sections]
                    #:when (and (<= (section-va s) rva) (< rva (+ (section-va s) (section-vsize s)))))
          s)
        (error 'tilde->uncompressed "rva 0x~x is not in any section" rva)))
  (define (rva->file rva)
    (define s (section-of rva))
    (+ (section-rawptr s) (- rva (section-va s))))

  ; CLI header and metadata root (II.25.3.3, II.24.2.1)
  (define cli (rva->file (dir-rva 14)))
  (define md-rva (u32 orig (+ cli 8)))
  (define md (rva->file md-rva))
  (define version-len (u32 orig (+ md 12)))
  (define stream-count (u16 orig (+ md 18 version-len)))
  (define (stream-name h)
    (let loop ([e (+ h 8)])
      (if (zero? (bytes-ref orig e))
          (subbytes orig (+ h 8) e)
          (loop (+ e 1)))))
  ; (header-offset . name) for each stream header, in file order
  (define headers
    (let loop ([i 0] [h (+ md 20 version-len)] [acc '()])
      (if (= i stream-count)
          (reverse acc)
          (let ([name (stream-name h)])
            ; name plus its null, padded to 4 bytes
            (loop (+ i 1)
                  (+ h 8 (* 4 (quotient (+ (bytes-length name) 4) 4)))
                  (cons (cons h name) acc))))))
  (define tilde-hdr
    (or (for/first ([hd headers] #:when (equal? (cdr hd) #"#~")) (car hd))
        (error 'tilde->uncompressed "no #~ stream")))
  (define tilde (+ md (u32 orig tilde-hdr)))
  (unless (zero? (bitwise-and (bytes-ref orig (+ tilde 6)) #x40))
    (error 'tilde->uncompressed "HeapSizes already has the 0x40 flag"))

  ; the table rows start after the #~ header (24 bytes) and one row count per present table.
  ; The 4 bytes that 0x40 adds go there, followed by the pointer tables and the new counts.
  (define valid (integer-bytes->integer orig #f #f (+ tilde 8) (+ tilde 16)))
  (define present-ids (for/list ([i (in-range 64)] #:when (bitwise-bit-set? valid i)) i))
  (define table-count (length present-ids))
  (define p-file (+ tilde 24 (* 4 table-count)))
  (define p-rva (+ md-rva (- p-file md)))
  ; a pointer table whose target has no rows is left out, like any absent table
  (define ptrs (for/list ([spec (in-list pointer-specs)]
                          #:when (and (memq (car spec) pointer-tables)
                                      (positive? (table-row-count rdr (cadddr spec)))))
                 (make-pointer rdr spec)))
  ; row count by table id; the new tables take the ids that are not yet present
  (define counts
    (for/fold ([h (for/hasheqv ([id (in-list present-ids)] [j (in-naturals)])
                    (values id (u32 orig (+ tilde 24 (* 4 j)))))])
              ([p (in-list ptrs)])
      (hash-set h (ptr-id p) (ptr-rows p))))
  (define counts-bytes
    (apply bytes-append
           (for/list ([id (in-list (sort (hash-keys counts) <))])
             (integer->integer-bytes (hash-ref counts id) 4 #f #f))))
  (define new-valid
    (for/fold ([v valid]) ([p (in-list ptrs)]) (bitwise-ior v (arithmetic-shift 1 (ptr-id p)))))
  ; the metadata grows by the 4 extra bytes, the new counts and the pointer rows
  (define delta
    (+ 4
       (- (bytes-length counts-bytes) (* 4 table-count))
       (for/sum ([p (in-list ptrs)]) (bytes-length (ptr-data p)))))
  (define text (section-of p-rva))
  (define raw-end (+ (section-rawptr text) (section-rawsize text)))
  (unless (and (<= (section-rawptr text) p-file) (< p-file (- raw-end delta)))
    (error 'tilde->uncompressed "table rows are not in the raw data of .text"))
  (define text-end-rva (+ (section-va text) (section-vsize text)))
  ; any RVA in the moved part of .text
  (define (moves? rva) (and (<= p-rva rva) (< rva text-end-rva)))
  (bytes-copy! img (+ tilde 8) (integer->integer-bytes new-valid 8 #f #f))


  ; RVA fields are written from the original bytes, so a field visited twice gets the same value
  (define (bump-rva! off)
    (define r (u32 orig off))
    (when (moves? r) (put-u32! img off (+ r delta))))
  ; import lookup entries; a set high bit marks an ordinal, not an RVA
  (define (bump-lookup! off)
    (define e (u32 orig off))
    (when (and (zero? (bitwise-and e #x80000000)) (moves? e))
      (put-u32! img off (+ e delta))))

  ; data directory RVAs and the entry point
  (for ([i (in-range 16)]) (bump-rva! (+ dirs (* 8 i))))
  (bump-rva! entry-field)

  ; the metadata and .text grow by delta
  (put-u32! img (+ cli 12) (+ (u32 orig (+ cli 12)) delta))
  (put-u32! img (+ (section-hdr text) 8) (+ (section-vsize text) delta))

  ; stream headers: #~ becomes #-, grows by delta and carries the flag, streams after it move
  (for ([hd headers])
    (define h (car hd))
    (cond
      [(equal? (cdr hd) #"#~")
       (put-u32! img (+ h 4) (+ (u32 orig (+ h 4)) delta))
       (bytes-set! img (+ h 9) (char->integer #\-))]
      [(> (+ md (u32 orig h)) p-file)
       (put-u32! img h (+ (u32 orig h) delta))]))
  (bytes-set! img (+ tilde 6) (bitwise-ior (bytes-ref orig (+ tilde 6)) #x40))

  ; the only tables that hold RVAs are MethodDef (column 0) and FieldRVA (column 0)
  (for ([name '(methoddef fieldrva)])
    (define td (hash-ref tables name #f))
    (when td
      (for ([i (in-range (table-data-row-count td))])
        (bump-rva! (+ (table-data-start-offset td) (* i (table-data-row-size td)))))))

  ; import directory (II.6.4). ILT and IAT hold hint/name RVAs.
  (define (walk-lookup! rva)
    (let loop ([off (rva->file rva)])
      (unless (zero? (u32 orig off))
        (bump-lookup! off)
        (loop (+ off 4)))))
  (let loop ([desc (rva->file (dir-rva 1))])
    (define oft (u32 orig desc))
    (define name (u32 orig (+ desc 12)))
    (define ft (u32 orig (+ desc 16)))
    (unless (and (zero? oft) (zero? name) (zero? ft))
      (bump-rva! desc)
      (bump-rva! (+ desc 12))
      (bump-rva! (+ desc 16))
      (walk-lookup! (if (zero? oft) ft oft))
      (walk-lookup! ft)
      (loop (+ desc 20))))

  ; base relocations (II.25.2.1 / .reloc). Only HIGHLOW (3) and ABSOLUTE padding (0) occur here.
  (define reloc-start (rva->file (dir-rva 5)))
  (define reloc-end (+ reloc-start (dir-size 5)))
  (let loop ([blk reloc-start])
    (when (< blk reloc-end)
      (define page (u32 orig blk))
      (define block-size (u32 orig (+ blk 4)))
      (for ([e (in-range (+ blk 8) (+ blk block-size) 2)])
        (define entry (u16 orig e))
        (define type (arithmetic-shift entry -12))
        (define off (bitwise-and entry #xFFF))
        (case type
          [(0) (void)]
          [(3)
           (let* ([site (+ page off)]
                  [site-file (rva->file site)]
                  [target (u32 orig site-file)])
             ; the stored address points at its target, so it moves with the target
             (when (moves? (- target image-base))
               (put-u32! img site-file (+ target delta)))
             (when (moves? site)
               (unless (< (+ off delta) #x1000)
                 (error 'tilde->uncompressed "relocation at 0x~x leaves its page" site))
               (put-u16! img e (bitwise-ior (arithmetic-shift type 12) (+ off delta)))))]
          [else (error 'tilde->uncompressed "unsupported relocation type ~a" type)]))
      (loop (+ blk block-size))))

  ; .text gives up delta bytes of zero padding at the end of its raw data. The edits are in
  ; original file offsets: the row counts are replaced, the 4 extra bytes go after them, each
  ; pointer table goes before the table it indexes, and the padding is dropped.
  (unless (and (<= (+ (section-rawptr text) (section-vsize text) delta) raw-end)
               (equal? (subbytes orig (- raw-end delta) raw-end) (make-bytes delta 0)))
    (error 'tilde->uncompressed ".text has no zero padding to give up"))
  ; (start end replacement); sort is stable, so the 4 extra bytes stay ahead of a pointer table
  ; that starts at the same offset
  (define edits
    (sort
     (append
      (list (list (+ tilde 24) p-file counts-bytes)
            (list p-file p-file (make-bytes 4 0))
            (list (- raw-end delta) raw-end #""))
      (for/list ([p (in-list ptrs)])
        (define start (table-data-start-offset (hash-ref tables (ptr-target p))))
        (list start start (ptr-data p))))
     < #:key car))
  (let loop ([es edits] [cursor 0] [acc '()])
    (cond
      [(null? es) (apply bytes-append (reverse (cons (subbytes img cursor) acc)))]
      [else
       (define e (car es))
       (loop (cdr es) (cadr e)
             (cons (caddr e) (cons (subbytes img cursor (car e)) acc)))])))
