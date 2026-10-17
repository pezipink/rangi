#lang racket/base
; Win32 resource directory in the .rsrc section (PE/COFF, "The .rsrc Section"). This module knows
; nothing about CLI metadata. It takes entries with 16-bit integer type, name, and language IDs,
; and returns the chunks of the .rsrc section.
(require racket/list
         "../private/binary.rkt"
         "constants.rkt"
         "model.rkt")
(provide (struct-out win32-entry) win32-resource-chunks rsrc-tree-chunk-name)

; type, name, lang: 16-bit integer IDs; bytes: the resource data
(struct win32-entry (type name lang bytes))

(define rsrc-tree-chunk-name 'rsrc-tree)

; Resource Directory Table: a 16-byte header, then one 8-byte entry per ID (.rsrc, Resource
; Directory Table and Resource Directory Entries)
(define directory-header-size 16)
(define directory-entry-size 8)
; Resource Data Entry: RVA, size, code page, reserved (.rsrc, Resource Data Entry)
(define data-entry-size 16)
; the high bit of an entry's offset marks a subdirectory; a clear bit marks a Resource Data Entry
(define subdirectory-flag #x80000000)

(define (directory-size n-entries)
  (+ directory-header-size (* directory-entry-size n-entries)))

; a Resource Directory Table with only ID entries. Each entry is (cons id offset-field), and the
; table counts its entries as NumberOfIdEntries. Named entries are not written.
(define (directory-table entries)
  (bytes-append (le 0 4) (le 0 4) (le 0 2) (le 0 2) (le 0 2) (le (length entries) 2)
                (apply bytes-append
                       (for/list ([e (in-list entries)])
                         (bytes-append (le (car e) 4) (le (cdr e) 4))))))

(define (entry-key e)
  (list (win32-entry-type e) (win32-entry-name e) (win32-entry-lang e)))

; lexicographic order on (type, name, language), each ascending
(define (key<? a b)
  (cond [(null? a) #f]
        [(< (car a) (car b)) #t]
        [(> (car a) (car b)) #f]
        [else (key<? (cdr a) (cdr b))]))

(define (sum xs) (apply + xs))

; start offsets of blocks laid out back to back from start, one per size
(define (starts-from start sizes)
  (let loop ([sizes sizes] [off start] [acc '()])
    (if (null? sizes)
        (reverse acc)
        (loop (cdr sizes) (+ off (car sizes)) (cons off acc)))))

(define (sub xs start n) (take (drop xs start) n))

(define (rsrc-data-sym i) (string->symbol (format "rsrc-data:~a" i)))

; Returns the chunks of the .rsrc section: the directory tree first, so its offset is the section
; start, then one chunk per resource in the same order as the Resource Data Entries. The tree
; chunk's data entries hold rva32 fixups to those chunks, so the RVAs are image RVAs.
(define (win32-resource-chunks entries)
  (for* ([e (in-list entries)] [id (in-list (entry-key e))])
    (unless (and (exact-integer? id) (<= 0 id #xFFFF))
      (error 'rangi "Win32 resource ID ~a is not a 16-bit integer" id)))
  ; the directory levels are type, then name, then language, and each level holds IDs in ascending
  ; order, since no named entries are written
  (define sorted (sort entries (λ (a b) (key<? (entry-key a) (entry-key b)))))
  (define dup (check-duplicates sorted #:key entry-key))
  (when dup (error 'rangi "duplicate Win32 resource ~s" (entry-key dup)))
  (define tree
    (for/list ([tg (in-list (group-by win32-entry-type sorted))])
      (cons (win32-entry-type (car tg)) (group-by win32-entry-name tg))))
  ; names is every name group, in order; each group is that name's entries by language
  (define names (append-map cdr tree))
  (define root-size (directory-size (length tree)))
  (define type-sizes (for/list ([t (in-list tree)]) (directory-size (length (cdr t)))))
  (define type-offs (starts-from root-size type-sizes))
  (define name-start (+ root-size (sum type-sizes)))
  (define name-sizes (for/list ([g (in-list names)]) (directory-size (length g))))
  (define name-offs (starts-from name-start name-sizes))
  (define data-start (+ name-start (sum name-sizes)))
  (define data-offs
    (for/list ([i (in-range (length sorted))]) (+ data-start (* data-entry-size i))))
  (define first-name-of-type
    (starts-from 0 (for/list ([t (in-list tree)]) (length (cdr t)))))
  (define first-entry-of-name (starts-from 0 (map length names)))

  (define root-bytes
    (directory-table (for/list ([t (in-list tree)] [off (in-list type-offs)])
                       (cons (car t) (bitwise-ior off subdirectory-flag)))))
  (define type-dir-bytes
    (for/list ([t (in-list tree)] [first-g (in-list first-name-of-type)])
      (define n (length (cdr t)))
      (directory-table
       (for/list ([g (in-list (sub names first-g n))] [off (in-list (sub name-offs first-g n))])
         (cons (win32-entry-name (car g)) (bitwise-ior off subdirectory-flag))))))
  (define name-dir-bytes
    (for/list ([g (in-list names)] [first-e (in-list first-entry-of-name)])
      (directory-table
       (for/list ([e (in-list g)] [off (in-list (sub data-offs first-e (length g)))])
         (cons (win32-entry-lang e) off)))))
  ; RVA is zero here; the rva32 fixup fills it once the payload chunk has an address
  (define data-entry-bytes
    (for/list ([e (in-list sorted)])
      (bytes-append (le 0 4) (le (bytes-length (win32-entry-bytes e)) 4) (le 0 4) (le 0 4))))
  (define tree-bytes
    (apply bytes-append root-bytes (append type-dir-bytes name-dir-bytes data-entry-bytes)))
  (define fixups
    (for/list ([off (in-list data-offs)] [i (in-naturals)])
      (fixup off 'rva32 (rsrc-data-sym i))))
  (cons (chunk rsrc-tree-chunk-name dword-align tree-bytes fixups)
        (for/list ([e (in-list sorted)] [i (in-naturals)])
          (chunk (rsrc-data-sym i) dword-align (win32-entry-bytes e) '()))))
