#lang racket/base
; Structural invariants of an emitted image (verification L5). The PE, section, and metadata
; stream layout is parsed from the bytes here, so a reader bug cannot hide a writer bug. Table
; layouts come from the L3 dump, and row offsets and sizes come from the reader, whose
; table header is checked against the bytes.
(require racket/list racket/port racket/string
         "../../src/cli-reader.rkt" "metadata-dump.rkt")
(provide lint-image)

(struct section (name va vsize raw-size raw-ptr chars))
(struct pe-image (raw sections base entry dirs size-of-image))

(define (expect fail! ok? fmt . args)
  (unless ok? (apply fail! fmt args)))

(define (power-of-two? n) (and (> n 0) (zero? (bitwise-and n (- n 1)))))
(define (align n a) (* a (quotient (+ n a -1) a)))

; returns the problems found as strings; an empty list means every invariant holds
(define (lint-image path)
  (define problems '())
  (define (fail! fmt . args)
    (set! problems (cons (apply format fmt args) problems)))
  (with-handlers ([exn:fail? (λ (e) (fail! "could not parse image: ~a" (exn-message e)))])
    (define raw (call-with-input-file path port->bytes))
    (define img (check-pe raw fail!))
    (when img
      (define cli (check-cli img fail!))
      (when cli
        (check-metadata img (car cli) (cadr cli) (caddr cli) (read-file path) fail!)
        (check-entry img fail!))))
  (reverse problems))

(define (read-section raw p)
  (section (string-trim (bytes->string/latin-1 (subbytes raw p (+ p 8))) "\0" #:left? #f)
           (le raw (+ p 12) 4) (le raw (+ p 8) 4) (le raw (+ p 16) 4) (le raw (+ p 20) 4)
           (le raw (+ p 36) 4)))

(define (rva->section secs rva)
  (findf (λ (s) (and (<= (section-va s) rva) (< rva (+ (section-va s) (section-vsize s)))))
         secs))

(define (rva->off img rva)
  (define s (rva->section (pe-image-sections img) rva))
  (and s (+ (section-raw-ptr s) (- rva (section-va s)))))

; the NUL-terminated ASCII string at a file offset, or #f when none is found before the end
(define (cstring-at raw off)
  (define end (for/first ([i (in-range off (bytes-length raw))] #:when (zero? (bytes-ref raw i))) i))
  (and end (bytes->string/latin-1 (subbytes raw off end))))

(define (check-pe raw fail!)
  (define len (bytes-length raw))
  (define lfanew (and (>= len #x40) (le raw #x3C 4)))
  (cond
    [(not (and lfanew (<= (+ lfanew 24) len)))
     (fail! "file is too short for the DOS and COFF headers") #f]
    [(not (equal? (subbytes raw lfanew (+ lfanew 4)) #"PE\0\0"))
     (fail! "missing PE signature at e_lfanew ~a" lfanew) #f]
    [else
     (define coff (+ lfanew 4))
     (define nsec (le raw (+ coff 2) 2))
     (define opt-size (le raw (+ coff 16) 2))
     (define opt (+ coff 20))
     (define sec-start (+ opt opt-size))
     (cond
       [(or (< opt-size 224) (> (+ sec-start (* 40 nsec)) len))
        (fail! "optional header or section table is outside the file") #f]
       [else
        (define (field off size) (le raw (+ opt off) size))
        (define secs
          (for/list ([i (in-range nsec)]) (read-section raw (+ sec-start (* 40 i)))))
        (define file-align (field 36 4))
        (define sec-align (field 32 4))
        (define size-of-headers (field 60 4))
        (define size-of-image (field 56 4))
        (define image-base (field 28 4))
        (define entry (field 16 4))
        (define (sum-raw bit)
          (for/sum ([s (in-list secs)] #:when (bitwise-bit-set? (section-chars s) bit))
            (section-raw-size s)))
        (define (first-va bit)
          (define s (findf (λ (s) (bitwise-bit-set? (section-chars s) bit)) secs))
          (if s (section-va s) 0))

        (expect fail! (= (field 0 2) #x10B) "optional header magic is not PE32")
        (expect fail! (= (le raw 0 2) #x5A4D) "DOS header does not start with MZ")
        (expect fail! (= (le raw coff 2) #x14C) "machine is not i386")
        (expect fail! (bitwise-bit-set? (le raw (+ coff 18) 2) 1)
                "COFF characteristics ~x do not set EXECUTABLE_IMAGE" (le raw (+ coff 18) 2))
        (expect fail! (memv (field 68 2) '(2 3))
                "Subsystem ~a is not Windows GUI or console" (field 68 2))
        (expect fail! (and (power-of-two? file-align) (<= #x200 file-align #x10000))
                "FileAlignment ~x is not a power of two between 0x200 and 0x10000" file-align)
        (expect fail! (and (power-of-two? sec-align) (>= sec-align file-align))
                "SectionAlignment ~x is not a power of two >= FileAlignment" sec-align)
        (expect fail! (zero? (modulo image-base #x10000)) "ImageBase ~x is not 64K aligned" image-base)
        (expect fail! (= size-of-headers (align (+ sec-start (* 40 nsec)) file-align))
                "SizeOfHeaders ~x is not the header size rounded to FileAlignment" size-of-headers)
        (expect fail! (= (field 4 4) (sum-raw 5))
                "SizeOfCode ~x does not match the code sections" (field 4 4))
        (expect fail! (= (field 8 4) (sum-raw 6))
                "SizeOfInitializedData ~x does not match the initialized data sections" (field 8 4))
        (expect fail! (= (field 20 4) (first-va 5))
                "BaseOfCode ~x is not the first code section" (field 20 4))
        (expect fail! (= (field 24 4) (first-va 6))
                "BaseOfData ~x is not the first initialized data section" (field 24 4))

        (for ([s (in-list secs)])
          (define name (section-name s))
          (expect fail! (bitwise-bit-set? (section-chars s) 30)
                  "section ~a is not readable" name)
          (expect fail! (zero? (modulo (section-va s) sec-align))
                  "section ~a RVA ~x is not SectionAlignment aligned" name (section-va s))
          (expect fail! (and (zero? (modulo (section-raw-ptr s) file-align))
                             (zero? (modulo (section-raw-size s) file-align)))
                  "section ~a raw data is not FileAlignment aligned" name)
          (expect fail! (and (>= (section-raw-ptr s) size-of-headers)
                             (<= (+ (section-raw-ptr s) (section-raw-size s)) len))
                  "section ~a raw data is outside the file" name)
          (expect fail! (<= (section-vsize s) (align (section-raw-size s) file-align))
                  "section ~a VirtualSize ~a exceeds its raw data" name (section-vsize s)))
        (for ([a (in-list secs)] [b (in-list (if (pair? secs) (cdr secs) '()))])
          (expect fail! (>= (section-va b) (+ (section-va a) (align (section-vsize a) sec-align)))
                  "sections ~a and ~a overlap or are out of order" (section-name a) (section-name b)))
        (when (pair? secs)
          (define last-s (last secs))
          (expect fail! (= size-of-image (align (+ (section-va last-s) (section-vsize last-s)) sec-align))
                  "SizeOfImage ~x does not end at the last section" size-of-image))

        (define es (rva->section secs entry))
        (expect fail! (and es (bitwise-bit-set? (section-chars es) 5))
                "AddressOfEntryPoint ~x is not in a code section" entry)
        ; the loader maps the entry stub with the section's protection, so it must be readable
        ; and executable (IMAGE_SCN_MEM_EXECUTE, IMAGE_SCN_MEM_READ)
        (expect fail! (and es (bitwise-bit-set? (section-chars es) 29)
                           (bitwise-bit-set? (section-chars es) 30))
                "entry section ~a is not readable and executable" (and es (section-name es)))

        (define dirs
          (for/hash ([i (in-range 16)])
            (values i (cons (field (+ 96 (* 8 i)) 4) (field (+ 100 (* 8 i)) 4)))))
        (expect fail! (= (field 92 4) 16) "NumberOfRvaAndSizes is not 16")
        (expect fail! (not (and (bitwise-bit-set? (le raw (+ coff 18) 2) 0) (> (car (hash-ref dirs 5)) 0)))
                "COFF says relocations are stripped, but a base relocation directory is present")
        (for ([(i d) (in-hash dirs)] #:when (> (car d) 0))
          (define s (rva->section secs (car d)))
          (expect fail! (and s (<= (+ (car d) (cdr d)) (+ (section-va s) (section-vsize s))))
                  "data directory ~a (RVA ~x, size ~a) is not inside a section" i (car d) (cdr d)))
        (pe-image raw secs image-base entry dirs size-of-image)])]))

(define (check-cli img fail!)
  (define raw (pe-image-raw img))
  (define cli (hash-ref (pe-image-dirs img) 14))
  (define off (and (> (car cli) 0) (rva->off img (car cli))))
  (cond
    [(not (and off (<= (+ off 72) (bytes-length raw))))
     (fail! "CLI header directory is missing or outside the file") #f]
    [else
     (expect fail! (= (le raw off 4) #x48) "CLI header cb is ~a, expected 72" (le raw off 4))
     (expect fail! (= (cdr cli) #x48) "CLI header directory size is ~a, expected 72" (cdr cli))
     (define flags (le raw (+ off 16) 4))
     (expect fail! (bitwise-bit-set? flags 0) "CLI flags ~x do not set ILONLY" flags)
     (define md-rva (le raw (+ off 8) 4))
     (define md-size (le raw (+ off 12) 4))
     (define md-sec (rva->section (pe-image-sections img) md-rva))
     (expect fail! (and md-sec (<= (+ md-rva md-size) (+ (section-va md-sec) (section-vsize md-sec))))
             "metadata RVA ~x (~a bytes) is not inside a section" md-rva md-size)
     (list md-rva md-size (le raw (+ off 20) 4))]))

; the entry stub is an indirect jump through the IAT, and its operand is an absolute address
; that the loader must fix up, so a HIGHLOW relocation has to cover it
(define (check-entry img fail!)
  (define raw (pe-image-raw img))
  (define entry (pe-image-entry img))
  (define eoff (rva->off img entry))
  (cond
    [(not (and eoff (<= (+ eoff 6) (bytes-length raw))))
     (fail! "entry point ~x is outside the file" entry)]
    [else
     (expect fail! (equal? (subbytes raw eoff (+ eoff 2)) (bytes #xFF #x25))
             "entry point ~x is not an indirect jump stub" entry)
     (define target (le raw (+ eoff 2) 4))
     (define imp (hash-ref (pe-image-dirs img) 1))
     (define ioff (and (> (car imp) 0) (rva->off img (car imp))))
     (define first-thunk (and ioff (le raw (+ ioff 16) 4)))
     (expect fail! (and first-thunk (= target (+ (pe-image-base img) first-thunk)))
             "entry stub jumps to ~x, which is not the import address table" target)
     (define dll-off (and ioff (rva->off img (le raw (+ ioff 12) 4))))
     (expect fail! (and dll-off (equal? (cstring-at raw dll-off) "mscoree.dll"))
             "import descriptor does not name mscoree.dll")
     (define hint-off (and first-thunk (rva->off img (le raw (rva->off img first-thunk) 4))))
     (expect fail! (and hint-off (equal? (cstring-at raw (+ hint-off 2)) "_CorExeMain"))
             "first import is not _CorExeMain")
     (define relocs (reloc-targets img fail!))
     (expect fail! (member (+ entry 2) relocs)
             "no base relocation covers the entry stub operand at ~x" (+ entry 2))]))

(define (reloc-targets img fail!)
  (define raw (pe-image-raw img))
  (define rd (hash-ref (pe-image-dirs img) 5))
  (define roff (and (> (car rd) 0) (rva->off img (car rd))))
  (cond
    [(not roff) (fail! "base relocation directory is missing") '()]
    [else
     (let loop ([p roff] [acc '()])
       (cond
         [(>= p (+ roff (cdr rd))) acc]
         [else
          (define page (le raw p 4))
          (define bsize (le raw (+ p 4) 4))
          (expect fail! (and (>= bsize 8) (zero? (modulo bsize 4)))
                  "relocation block for page ~x has size ~a" page bsize)
          (cond
            [(< bsize 8) acc]
            [else
             (define entries
               (for/list ([k (in-range (quotient (- bsize 8) 2))])
                 (le raw (+ p 8 (* 2 k)) 2)))
             (for ([e (in-list entries)])
               (expect fail! (memv (arithmetic-shift e -12) '(0 3))
                       "relocation type ~a is not HIGHLOW or padding" (arithmetic-shift e -12)))
             (define targets
               (for/list ([e (in-list entries)] #:when (= (arithmetic-shift e -12) 3))
                 (+ page (bitwise-and e #xFFF))))
             (for ([t (in-list targets)])
               (expect fail! (rva->section (pe-image-sections img) t)
                       "relocation target ~x is outside every section" t))
             (loop (+ p bsize) (append targets acc))])]))]))

(define (check-metadata img md-rva md-size entry-token rdr fail!)
  (define raw (pe-image-raw img))
  (define md (rva->off img md-rva))
  (cond
    [(not (and md (<= (+ md md-size) (bytes-length raw))))
     (fail! "metadata blob is outside the file")]
    [(< md-size 16) (fail! "metadata blob is too small for its root")]
    [else
     (define attrs (asm-reader-table-attributes rdr))
     (define (count-of name)
       (let ([td (hash-ref attrs name #f)]) (if td (table-data-row-count td) 0)))
     (define md-end (+ md md-size))
     (expect fail! (equal? (subbytes raw md (+ md 4)) #"BSJB")
             "metadata root does not start with BSJB")
     (expect fail! (and (= (le raw (+ md 4) 2) 1) (= (le raw (+ md 6) 2) 1))
             "metadata version is not 1.1")
     (define vlen (le raw (+ md 12) 4))
     (define sh (+ md 16 vlen))
     (expect fail! (and (zero? (modulo vlen 4)) (<= (+ sh 4) md-end))
             "metadata version length ~a is not padded or the root runs past the blob" vlen)
     (define streams
       (let loop ([p (+ sh 4)] [n (le raw (+ sh 2) 2)] [acc '()])
         (cond
           [(or (zero? n) (> (+ p 8) md-end)) (reverse acc)]
           [else
            (define name-end
              (let scan ([q (+ p 8)])
                (if (or (>= q md-end) (zero? (bytes-ref raw q))) q (scan (+ q 1)))))
            (define name (bytes->string/latin-1 (subbytes raw (+ p 8) name-end)))
            (loop (+ p 8 (align (+ (- name-end (+ p 8)) 1) 4)) (- n 1)
                  (cons (list name (le raw p 4) (le raw (+ p 4) 4)) acc))])))
     (for ([s (in-list streams)])
       (define name (car s))
       (define off (cadr s))
       (define size (caddr s))
       (expect fail! (zero? (modulo off 4)) "stream ~a offset ~a is not 4-byte aligned" name off)
       (expect fail! (zero? (modulo size 4)) "stream ~a size ~a is not 4-byte aligned" name size)
       (expect fail! (<= (+ off size) md-size) "stream ~a runs past the metadata blob" name))
     (expect fail! (= (length streams) (length (remove-duplicates (map car streams))))
             "duplicate metadata stream names")
     (define (stream-named n) (findf (λ (s) (equal? (car s) n)) streams))
     (define tilde (stream-named "#~"))
     (define strings (stream-named "#Strings"))
     (define blob (stream-named "#Blob"))
     (define guid (stream-named "#GUID"))
     (cond
       [(not (and tilde strings blob guid))
        (fail! "metadata is missing a required stream")]
       [else
        (check-heaps rdr strings blob guid fail!)
        (check-tables rdr raw (+ md (cadr tilde)) (caddr tilde) attrs count-of fail!)
        (check-entry-token raw attrs count-of entry-token img fail!)])]))

(define (check-heaps rdr strings blob guid fail!)
  (expect fail! (= (caddr strings) (bytes-length (asm-reader-string-heap rdr)))
          "#Strings size ~a disagrees with the reader" (caddr strings))
  (expect fail! (= (caddr blob) (bytes-length (asm-reader-blob-heap rdr)))
          "#Blob size ~a disagrees with the reader" (caddr blob))
  (expect fail! (= (caddr guid) (bytes-length (asm-reader-guid-heap rdr)))
          "#GUID size ~a disagrees with the reader" (caddr guid)))

(define (check-tables rdr raw t tsize attrs count-of fail!)
  (define heap-bits (bytes-ref raw (+ t 6)))
  (define valid (le raw (+ t 8) 8))
  (define sorted (le raw (+ t 16) 8))
  (define present (for/list ([i (in-range 64)] #:when (bitwise-bit-set? valid i)) i))
  (define header-len (+ 24 (* 4 (length present))))
  (define row-counts
    (for/list ([k (in-range (length present))]) (le raw (+ t 24 (* 4 k)) 4)))
  (define tds (sort (hash-values attrs) < #:key table-data-start-offset))
  (define data-len
    (for/sum ([td (in-list tds)]) (* (table-data-row-count td) (table-data-row-size td))))

  (expect fail! (< valid (expt 2 45)) "Valid mask ~x has bits above II.22" valid)
  ; the writer keeps rows in insertion order and marks no table as sorted
  (expect fail! (zero? sorted)
          "Sorted mask is ~x; the writer keeps insertion order and sets no Sorted bits" sorted)
  (expect fail! (= (if (bitwise-bit-set? heap-bits 0) 4 2) (asm-reader-string-index-size rdr))
          "string index width disagrees with the reader")
  (expect fail! (= (if (bitwise-bit-set? heap-bits 2) 4 2) (asm-reader-blob-index-size rdr))
          "blob index width disagrees with the reader")
  (expect fail! (= (if (bitwise-bit-set? heap-bits 1) 4 2) (asm-reader-guid-index-size rdr))
          "GUID index width disagrees with the reader")
  (expect fail! (equal? (sort row-counts <)
                        (sort (for/list ([td (in-list tds)]) (table-data-row-count td)) <))
          "Valid mask row counts disagree with the reader")
  (expect fail! (<= (+ header-len data-len) tsize)
          "#~ stream is ~a bytes but its tables need ~a" tsize (+ header-len data-len))
  (expect fail! (< (- tsize header-len data-len) 4)
          "#~ stream has more than 3 bytes of trailing padding")
  (when (pair? tds)
    (expect fail! (= (table-data-start-offset (car tds)) (+ t header-len))
            "first table starts at ~x, expected ~x" (table-data-start-offset (car tds)) (+ t header-len))
    (for ([a (in-list tds)] [b (in-list (cdr tds))])
      (expect fail! (= (table-data-start-offset b)
                       (+ (table-data-start-offset a)
                          (* (table-data-row-count a) (table-data-row-size a))))
              "tables are not contiguous after ~a" (table-data-start-offset a))))

  (define heap-lens
    (hash 'str (bytes-length (asm-reader-string-heap rdr))
          'blob (bytes-length (asm-reader-blob-heap rdr))
          'guid (bytes-length (asm-reader-guid-heap rdr))))
  (for ([(name td) (in-hash attrs)])
    (cond
      [(hash-ref layouts name #f)
       => (λ (cols) (check-indexes rdr raw name td cols heap-lens count-of fail!))]
      [(memq name '(field param)) (void)]
      [else (fail! "table ~a has no layout in the lint" name)])))

; every heap index, simple index, and coded index must be in range
(define (check-indexes rdr raw name td cols heap-lens count-of fail!)
  (define size (table-data-row-size td))
  (define cols-size (for/sum ([c (in-list cols)]) (column-size rdr (cadr c))))
  (expect fail! (= cols-size size)
          "~a rows are ~a bytes but the layout gives ~a" name size cols-size)
  (for ([i (in-range (table-data-row-count td))])
    (define base (+ (table-data-start-offset td) (* i size)))
    (for/fold ([pos base]) ([c (in-list cols)])
      (define kind (cadr c))
      (define w (column-size rdr kind))
      (define v (le raw pos w))
      (expect fail! (index-ok? kind v heap-lens count-of)
              "~a row ~a column ~a has index ~a out of range" name (+ i 1) (car c) v)
      (+ pos w))
    (void)))

(define (index-ok? kind v heap-lens count-of)
  (cond
    [(eq? kind 'str) (< v (hash-ref heap-lens 'str))]
    [(eq? kind 'blob) (< v (hash-ref heap-lens 'blob))]
    [(eq? kind 'guid) (<= v (quotient (hash-ref heap-lens 'guid) 16))]
    ; simple columns are list starts, which may point one past the last row when a list is empty
    [(eq? (car kind) 'simple) (<= v (+ 1 (count-of (cadr kind))))]
    [(eq? (car kind) 'coded)
     (define spec (hash-ref coded-specs (cadr kind)))
     (define tag (bitwise-and v (sub1 (arithmetic-shift 1 (car spec)))))
     (define row (arithmetic-shift v (- (car spec))))
     (and (< tag (length (cdr spec)))
          (<= row (count-of (list-ref (cdr spec) tag))))]
    [else #t]))

; the entry point must be a MethodDef with a body
(define (check-entry-token raw attrs count-of entry-token img fail!)
  (define mtd (hash-ref attrs 'methoddef #f))
  (define mcount (count-of 'methoddef))
  (define rid (bitwise-and entry-token #xFFFFFF))
  (expect fail! (= (arithmetic-shift entry-token -24) 6)
          "entry point token ~x is not a MethodDef token" entry-token)
  (expect fail! (<= 1 rid mcount) "entry point token ~x is outside MethodDef" entry-token)
  (when mtd
    (define size (table-data-row-size mtd))
    (define start (table-data-start-offset mtd))
    (for ([i (in-range mcount)])
      (define rva (le raw (+ start (* i size)) 4))
      (when (> rva 0)
        (check-body img raw rva count-of fail!)))
    (when (<= 1 rid mcount)
      (expect fail! (> (le raw (+ start (* (- rid 1) size)) 4) 0)
              "entry point method ~a has no body" rid))))

; II.25.4 tiny (flags 2) and fat (flags 3) method headers
(define (check-body img raw rva count-of fail!)
  (define off (rva->off img rva))
  (cond
    [(not (and off (< off (bytes-length raw))))
     (fail! "method body RVA ~x is outside every section" rva)]
    [else
     (define b0 (bytes-ref raw off))
     (define-values (start size)
       (case (bitwise-and b0 3)
         [(2) (values (+ off 1) (arithmetic-shift b0 -2))]
         [(3) (values (+ off (* 4 (arithmetic-shift (le raw off 2) -12))) (le raw (+ off 4) 4))]
         [else (values #f 0)]))
     (cond
       [(not start) (fail! "method body at ~x has an unknown header byte ~x" rva b0)]
       [(> (+ start size) (bytes-length raw)) (fail! "method body at ~x runs past the file" rva)]
       [else (check-il raw start (+ start size) rva count-of fail!)])]))

; the writer emits only these opcodes; any other byte is reported rather than guessed at
(define (check-il raw p end rva count-of fail!)
  (let loop ([p p])
    (cond
      [(= p end) (void)]
      [(> p end) (fail! "method body at ~x has an instruction past its code size" rva)]
      [else
       (case (bytes-ref raw p)
         [(#x2A #x58) (loop (+ p 1))]
         [(#x20) (loop (+ p 5))]
         [(#x28)
          (check-token raw (+ p 1) rva count-of fail!)
          (loop (+ p 5))]
         [else
          (fail! "method body at ~x uses opcode ~x, which the lint does not decode"
                 rva (bytes-ref raw p))
          (void)])])))

(define (check-token raw pos rva count-of fail!)
  (define tok (le raw pos 4))
  (define table (arithmetic-shift tok -24))
  (define rid (bitwise-and tok #xFFFFFF))
  (define name (case table [(#x0A) 'memberref] [(#x06) 'methoddef] [else #f]))
  (cond
    [(not name)
     (fail! "method body at ~x references token table ~x, which the lint does not decode" rva table)]
    [else
     (expect fail! (<= 1 rid (count-of name))
             "method body at ~x references missing ~a row ~a" rva name rid)]))
