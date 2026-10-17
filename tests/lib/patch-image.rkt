#lang racket/base
; Turns a #~ image into the same image with the uncompressed #- stream and HeapSizes flag 0x40.
; II.24.2.6 does not define the 4 bytes that 0x40 adds before the table rows. SRM reads them
; and ignores them (ReadMetadataTableHeader), so the decoded tables do not change.
; The insertion point is the first table row. Everything after it moves by 4 bytes, so the
; patch also updates every stored RVA and file position that points past it: PE header fields,
; the CLI header, stream headers, MethodDef and FieldRVA rows, the import directory and base
; relocations. The 4 bytes come from zero padding at the end of .text, so no raw size changes.
(require racket/port "../../src/cli-reader.rkt")
(provide tilde->uncompressed)

(struct section (va vsize rawsize rawptr hdr))

(define (u16 b o) (integer-bytes->integer b #f #f o (+ o 2)))
(define (u32 b o) (integer-bytes->integer b #f #f o (+ o 4)))
(define (put-u16! b o v) (bytes-copy! b o (integer->integer-bytes v 2 #f #f)))
(define (put-u32! b o v) (bytes-copy! b o (integer->integer-bytes v 4 #f #f)))

; path of a PE32 image with a #~ stream; returns the patched image as bytes
(define (tilde->uncompressed path)
  (define orig (call-with-input-file path port->bytes))
  (define img (bytes-copy orig))
  (define tables (asm-reader-table-attributes (read-file path)))

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

  ; the insertion point: after the #~ header (24 bytes) and one row count per present table
  (define valid (integer-bytes->integer orig #f #f (+ tilde 8) (+ tilde 16)))
  (define table-count (for/sum ([i (in-range 64)]) (if (bitwise-bit-set? valid i) 1 0)))
  (define p-file (+ tilde 24 (* 4 table-count)))
  (define p-rva (+ md-rva (- p-file md)))
  (define text (section-of p-rva))
  (define raw-end (+ (section-rawptr text) (section-rawsize text)))
  (unless (and (<= (section-rawptr text) p-file) (< p-file (- raw-end 4)))
    (error 'tilde->uncompressed "table rows are not in the raw data of .text"))
  (define text-end-rva (+ (section-va text) (section-vsize text)))
  ; any RVA in the moved part of .text
  (define (moves? rva) (and (<= p-rva rva) (< rva text-end-rva)))

  ; RVA fields are written from the original bytes, so a field visited twice gets the same value
  (define (bump-rva! off)
    (define r (u32 orig off))
    (when (moves? r) (put-u32! img off (+ r 4))))
  ; import lookup entries; a set high bit marks an ordinal, not an RVA
  (define (bump-lookup! off)
    (define e (u32 orig off))
    (when (and (zero? (bitwise-and e #x80000000)) (moves? e))
      (put-u32! img off (+ e 4))))

  ; data directory RVAs and the entry point
  (for ([i (in-range 16)]) (bump-rva! (+ dirs (* 8 i))))
  (bump-rva! entry-field)

  ; the metadata grows by 4 bytes, and so does .text
  (put-u32! img (+ cli 12) (+ (u32 orig (+ cli 12)) 4))
  (put-u32! img (+ (section-hdr text) 8) (+ (section-vsize text) 4))

  ; stream headers: #~ becomes #-, grows by 4 and carries the flag, streams after it move
  (for ([hd headers])
    (define h (car hd))
    (cond
      [(equal? (cdr hd) #"#~")
       (put-u32! img (+ h 4) (+ (u32 orig (+ h 4)) 4))
       (bytes-set! img (+ h 9) (char->integer #\-))]
      [(> (+ md (u32 orig h)) p-file)
       (put-u32! img h (+ (u32 orig h) 4))]))
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
               (put-u32! img site-file (+ target 4)))
             (when (moves? site)
               (unless (< (+ off 4) #x1000)
                 (error 'tilde->uncompressed "relocation at 0x~x leaves its page" site))
               (put-u16! img e (bitwise-ior (arithmetic-shift type 12) (+ off 4)))))]
          [else (error 'tilde->uncompressed "unsupported relocation type ~a" type)]))
      (loop (+ blk block-size))))

  ; drop 4 zero bytes from the end of .text's raw data and insert the new field at the table rows
  (unless (and (<= (+ (section-rawptr text) (section-vsize text)) (- raw-end 4))
               (equal? (subbytes orig (- raw-end 4) raw-end) #"\0\0\0\0"))
    (error 'tilde->uncompressed ".text has no zero padding to give up"))
  (bytes-append (subbytes img 0 p-file)
                (make-bytes 4 0)
                (subbytes img p-file (- raw-end 4))
                (subbytes img raw-end)))
