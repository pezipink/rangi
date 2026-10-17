#lang racket/base
; Import of _CorExeMain from mscoree.dll and the entry stub that jumps through
; its IAT slot (ECMA-335 II.25.3.3).
(require "../private/binary.rkt"
         "constants.rkt"
         "layout.rkt")
(provide mscoree-chunks)

(define hint-name-bytes (bytes-append (le 0 2) #"_CorExeMain\0"))
(define dll-name-bytes #"mscoree.dll\0")

; sizes in bytes of the import and entry-stub encodings (II.22.25 and II.25.3.3)
(define pe32-thunk-size 4)
(define pe32plus-thunk-size 8)
(define import-dir-entry-size 20)
; the directory table ends with a null entry, so two entries are emitted
(define import-dir-table-size (* 2 import-dir-entry-size))

; x86-64 entry stub: movabs rax, imm64 (48 A1) then jmp rax (FF E0)
(define stub-movabs-rax (bytes #x48 #xA1))
(define stub-jmp-rax (bytes #xFF #xE0))
; x86 entry stub: jmp [abs32] (FF 25)
(define stub-jmp-indirect (bytes #xFF #x25))

; returns (list iat import-dir lookup hint-name dll-name entry-stub) for the given
; PE format. Thunks are 4 bytes in PE32 and 8 bytes in PE32+ (II.22.25 and II.25.3.3).
(define (mscoree-chunks format)
  (define pe32+? (eq? format 'pe32+))
  (define thunk-size (if pe32+? pe32plus-thunk-size pe32-thunk-size))
  (define thunk-table (make-bytes (* 2 thunk-size) 0))
  (list
   (chunk 'iat dword-align thunk-table (list (fixup 0 'rva32 'hint-name)))
   ; the import directory's Name, ImportLookupTable, and ImportAddressTable RVA fields
   ; sit at offsets 12, 0, and 16 of the entry
   (chunk 'import-dir dword-align
          (make-bytes import-dir-table-size 0)
          (list (fixup 0 'rva32 'lookup)
                (fixup 12 'rva32 'dll-name)
                (fixup 16 'rva32 'iat)))
   (chunk 'lookup dword-align thunk-table (list (fixup 0 'rva32 'hint-name)))
   (chunk 'hint-name 1 hint-name-bytes '())
   (chunk 'dll-name 1 dll-name-bytes '())
   (if pe32+?
       ; FF 25 takes only a 32-bit operand, which cannot reach an IAT above 4 GB, so load the
       ; 64-bit slot with movabs and jump through rax. The operand needs a DIR64 relocation.
       (chunk 'entry-stub dword-align
              (bytes-append stub-movabs-rax (make-bytes (fixup-size 'va64) 0) stub-jmp-rax)
              (list (fixup 2 'va64 'iat)))
       ; FF 25 is jmp [abs32]; the operand is an absolute address, so it needs a base relocation
       (chunk 'entry-stub dword-align
              (bytes-append stub-jmp-indirect (make-bytes (fixup-size 'va32) 0))
              (list (fixup 2 'va32 'iat))))))
