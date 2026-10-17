#lang racket/base
; Import of _CorExeMain from mscoree.dll and the entry stub that jumps through
; its IAT slot (ECMA-335 II.25.3.3).
(require "../private/binary.rkt"
         "layout.rkt")
(provide mscoree-chunks)

(define hint-name-bytes (bytes-append (le 0 2) #"_CorExeMain\0"))
(define dll-name-bytes #"mscoree.dll\0")

; returns (list iat import-dir lookup hint-name dll-name entry-stub)
(define (mscoree-chunks)
  (list
   (chunk 'iat 4 (make-bytes 8 0) (list (fixup 0 'rva32 'hint-name)))
   (chunk 'import-dir 4
          (bytes-append (le 0 4) (le 0 4) (le 0 4) (le 0 4) (le 0 4) (make-bytes 20 0))
          (list (fixup 0 'rva32 'lookup)
                (fixup 12 'rva32 'dll-name)
                (fixup 16 'rva32 'iat)))
   (chunk 'lookup 4 (make-bytes 8 0) (list (fixup 0 'rva32 'hint-name)))
   (chunk 'hint-name 1 hint-name-bytes '())
   (chunk 'dll-name 1 dll-name-bytes '())
   ; FF 25 is jmp [abs32]; the operand is an absolute address, so it needs a base relocation
   (chunk 'entry-stub 4 (bytes-append (bytes #xFF #x25) (make-bytes 4 0))
          (list (fixup 2 'va32 'iat)))))
