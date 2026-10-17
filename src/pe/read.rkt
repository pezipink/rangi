#lang racket/base
; Reads the PE headers of a .exe or .dll (ECMA-335 II.25.2) and maps RVAs to file offsets.
; This module knows nothing about CLI metadata. It is part of the lazy reader, so keep it cheap.
(require "../private/binary.rkt"
         "constants.rkt")
(provide read-spec read-pe-headers rva->file-offset)

; only the first 0x40 bytes are needed; e_lfanew at 0x3C points at the PE header
(define ms-dos-header-spec
  `((header ,dos-header-size)))

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

(define (read-spec spec port)
  (make-hash
   (map (λ (x) (let ([id (car x)]
                     [size (cadr x)])
                 (cons id (read-bytes size port)))) spec)))

; Reads the headers from port, which must be at the start of the file. Returns a hash with
; 'ms-dos, 'pe, 'pe-opt and 'sec-headers. Leaves port just after the section headers.
(define (read-pe-headers port)
  (define dos-header (read-spec ms-dos-header-spec port))
  ; e_lfanew is the file offset of the PE signature
  (define pe-offset (bytes->uint-le (subbytes (hash-ref dos-header 'header)
                                              e-lfanew-offset
                                              (+ e-lfanew-offset e-lfanew-size))))
  (file-position port pe-offset)
  (define pe-headers (make-hash))
  (hash-set! pe-headers 'ms-dos dos-header)
  (hash-set! pe-headers 'pe (read-spec pe-file-header-spec port))
  (define opt-start (file-position port))
  (define opt-header-size (bytes->uint-le (hash-ref (hash-ref pe-headers 'pe) 'opt-header-size)))
  ; the magic tells PE32 and PE32+ apart
  (define magic (bytes->uint-le (peek-bytes 2 0 port)))
  (hash-set! pe-headers 'pe-opt
             (read-spec (if (= magic pe32plus-magic) pe32plus-opt-header-spec pe-opt-header-spec) port))
  ; section headers follow the optional header, whose real size is recorded in the file header
  (file-position port (+ opt-start opt-header-size))
  (define num-secs (bytes->uint-le (hash-ref (hash-ref pe-headers 'pe) 'num-secs)))
  (hash-set! pe-headers 'sec-headers
             (for/list ([i (in-range 0 num-secs)]) (read-spec pe-section-header-spec port)))
  pe-headers)

; File offset of rva, found in the section that contains it. Sections are searched in
; header order. For example, with .text at rva 0x2000 and raw data at 0x200, rva 0x2008
; is at file offset 0x208.
(define (rva->file-offset pe-headers rva)
  (or (for/first ([header (in-list (hash-ref pe-headers 'sec-headers))]
                  #:when (let ([va (bytes->uint-le (hash-ref header 'virt-address))])
                           (and (<= va rva) (< rva (+ va (bytes->uint-le (hash-ref header 'virt-size)))))))
        (+ (bytes->uint-le (hash-ref header 'ptr-raw)) (- rva (bytes->uint-le (hash-ref header 'virt-address)))))
      (error 'rva->file-offset "rva 0x~x is not in any section" rva)))
