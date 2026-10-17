#lang racket/base
; Import of _CorExeMain from mscoree.dll and the entry stub that jumps through
; its IAT slot (ECMA-335 II.25.3.3).
(require "../private/binary.rkt"
         "layout.rkt")
(provide mscoree-chunks)

(define hint-name-bytes (bytes-append (le 0 2) #"_CorExeMain\0"))
(define dll-name-bytes #"mscoree.dll\0")

; returns (list iat import-dir lookup hint-name dll-name entry-stub)
(define (mscoree-chunks image-base)
  (list
   (linked-chunk 'iat 4 8
                 (λ (rva-of) (bytes-append (le (rva-of 'hint-name) 4) (le 0 4))))
   (linked-chunk 'import-dir 4 #x28
                 (λ (rva-of)
                   (bytes-append (le (rva-of 'lookup) 4) (le 0 4) (le 0 4)
                                 (le (rva-of 'dll-name) 4) (le (rva-of 'iat) 4)
                                 (make-bytes 20 0))))
   (linked-chunk 'lookup 4 8
                 (λ (rva-of) (bytes-append (le (rva-of 'hint-name) 4) (le 0 4))))
   (bytes-chunk 'hint-name 1 hint-name-bytes)
   (bytes-chunk 'dll-name 1 dll-name-bytes)
   ; FF 25 is jmp [abs32]; the operand is an absolute address, so it needs a base relocation
   (linked-chunk 'entry-stub 4 6
                 (λ (rva-of)
                   (bytes-append (bytes #xFF #x25) (le (+ image-base (rva-of 'iat)) 4)))
                 '(2))))
