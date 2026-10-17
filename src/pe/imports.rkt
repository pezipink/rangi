#lang racket/base
; Import of _CorExeMain from mscoree.dll and the entry stub that jumps through
; its IAT slot (ECMA-335 II.25.3.3).
(require "../private/binary.rkt"
         "layout.rkt")
(provide mscoree-chunks)

(define hint-name-bytes (bytes-append (le 0 2) #"_CorExeMain\0"))
(define dll-name-bytes #"mscoree.dll\0")

; returns (list iat import-dir lookup hint-name dll-name entry-stub) for the given
; PE format. Thunks are 4 bytes in PE32 and 8 bytes in PE32+ (II.22.25 and II.25.3.3).
(define (mscoree-chunks format)
  (define pe32+? (eq? format 'pe32+))
  (define thunk-size (if pe32+? 8 4))
  (define thunk-table (make-bytes (* 2 thunk-size) 0))
  (list
   (chunk 'iat 4 thunk-table (list (fixup 0 'rva32 'hint-name)))
   (chunk 'import-dir 4
          (bytes-append (le 0 4) (le 0 4) (le 0 4) (le 0 4) (le 0 4) (make-bytes 20 0))
          (list (fixup 0 'rva32 'lookup)
                (fixup 12 'rva32 'dll-name)
                (fixup 16 'rva32 'iat)))
   (chunk 'lookup 4 thunk-table (list (fixup 0 'rva32 'hint-name)))
   (chunk 'hint-name 1 hint-name-bytes '())
   (chunk 'dll-name 1 dll-name-bytes '())
   (if pe32+?
       ; FF 25 takes only a 32-bit operand, which cannot reach an IAT above 4 GB, so load the
       ; 64-bit slot with movabs and jump through rax. The operand needs a DIR64 relocation.
       (chunk 'entry-stub 4 (bytes-append (bytes #x48 #xA1) (make-bytes 8 0) (bytes #xFF #xE0))
              (list (fixup 2 'va64 'iat)))
       ; FF 25 is jmp [abs32]; the operand is an absolute address, so it needs a base relocation
       (chunk 'entry-stub 4 (bytes-append (bytes #xFF #x25) (make-bytes 4 0))
              (list (fixup 2 'va32 'iat))))))
