#lang racket/base
; Named values for the PE/COFF headers, section flags, and data directories (ECMA-335 II.25.2
; and II.25.3 refer to the PE/COFF specification for them). The writer and the reader both use
; these, so each value is written down once. Nothing here depends on CLI metadata.
(provide (all-defined-out))

; ---------------------------------------------------------------------------
; MS-DOS stub and PE signature

(define dos-header-size #x40)
(define e-lfanew-offset #x3C)
(define e-lfanew-size 4)
; where this writer puts the PE signature, which is the value of e_lfanew
(define pe-header-offset #x80)
(define pe-signature-bytes #"PE\0\0")
(define dos-and-signature-size (+ pe-header-offset (bytes-length pe-signature-bytes)))

; ---------------------------------------------------------------------------
; COFF file header

(define coff-header-size 20)
(define machine-i386 #x14C)
(define machine-amd64 #x8664)
(define image-file-executable-image #x0002)
(define image-file-large-address-aware #x0020)
(define image-file-32bit-machine #x0100)
(define image-file-dll #x2000)
(define pe32-characteristics
  (bitwise-ior image-file-executable-image image-file-32bit-machine))
(define pe32plus-characteristics
  (bitwise-ior image-file-executable-image image-file-large-address-aware))

; ---------------------------------------------------------------------------
; optional header

(define pe32-opt-header-size #xE0)
(define pe32plus-opt-header-size #xF0)
(define pe32-magic #x10B)
(define pe32plus-magic #x20B)
(define linker-major-version 6)
(define linker-minor-version 5)
(define os-major-version 4)
(define subsystem-major-version 4)
(define subsystem-windows-gui 2)
(define subsystem-windows-cui 3)
(define stack-reserve-size #x100000)
(define stack-commit-size #x1000)
(define heap-reserve-size #x100000)
(define heap-commit-size #x1000)
(define number-of-data-dirs 16)
(define data-dir-entry-size 8)

(define dll-terminal-server-aware #x8000)
(define dll-no-seh #x0400)
(define dll-nx-compat #x0100)
(define dll-dynamic-base #x0040)
(define default-dll-characteristics
  (bitwise-ior dll-terminal-server-aware dll-no-seh dll-nx-compat dll-dynamic-base))

; data directory indices, in PE/COFF order
(define dir-import-table 1)
(define dir-resource-table 2)
(define dir-base-relocation-table 5)
(define dir-iat 12)
(define dir-clr-runtime-header 14)

; ---------------------------------------------------------------------------
; section table and section flags

(define section-header-size 40)
(define section-name-size 8)
(define scn-cnt-code #x20)
(define scn-cnt-initialized-data #x40)
(define scn-mem-discardable #x02000000)
(define scn-mem-execute #x20000000)
(define scn-mem-read #x40000000)
(define scn-mem-write #x80000000)
(define section-chars-text (bitwise-ior scn-cnt-code scn-mem-execute scn-mem-read))
(define section-chars-reloc
  (bitwise-ior scn-cnt-initialized-data scn-mem-discardable scn-mem-read))
; read-write initialized data, for static data (II.16)
(define section-chars-sdata
  (bitwise-ior scn-cnt-initialized-data scn-mem-read scn-mem-write))
; read-only initialized data for the Win32 resource tree (PE/COFF, The .rsrc Section)
(define section-chars-rsrc
  (bitwise-ior scn-cnt-initialized-data scn-mem-read))

; ---------------------------------------------------------------------------
; defaults for the images the writer emits

(define default-image-base-pe32 #x400000)
(define default-image-base-pe32+ #x140000000)
(define default-section-align #x2000)
(define default-file-align #x200)
; alignment of the import tables, base relocation blocks, and method bodies
(define dword-align 4)
