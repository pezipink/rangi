#lang racket/base
; Data model for PE images (ECMA-335 II.25.2 and II.25.3). This module knows nothing
; about CLI metadata. A chunk is a named blob of bytes with fixups: 4-byte holes that
; are filled in once every chunk has an RVA.
(provide (struct-out image-params)
         (struct-out chunk)
         (struct-out fixup)
         (struct-out digest)
         (struct-out section)
         (struct-out placement)
         (struct-out placed-section)
         (struct-out placed-image))

; format: 'pe32 or 'pe32+
; machine, characteristics, subsystem, dll-characteristics: the COFF and optional header values
; image-base, section-align, file-align: the optional header alignments
(struct image-params (format machine characteristics subsystem dll-characteristics
                             image-base section-align file-align))

; bytes: the chunk contents with zeros in each fixup hole
(struct chunk (name align bytes fixups))

; A field at offset inside the chunk, filled with the value for target (a chunk name):
;   'rva32       the RVA of target, 4 bytes
;   'va32        image-base plus the RVA of target, 4 bytes; the field needs a base relocation
;   'va64        image-base plus the RVA of target, 8 bytes; the field needs a DIR64 base relocation
;   'file-offset the file offset of target, 4 bytes
(struct fixup (offset kind target))

; A 16-byte field at offset holding the first 16 bytes of the SHA-256 of the
; chunk's rendered bytes at each (start . end) span. It is filled after the
; rva32 fixups, so a span may cover RVA fields. Spans must not cover the field itself.
(struct digest (offset spans))

; name: string; chars: section characteristics
(struct section (name chars chunks))

; rva: absolute RVA of the chunk; file-offset: where its bytes start in the file
(struct placement (chunk rva file-offset))

(struct placed-section (name chars rva vsize raw-ptr raw-size placements))

; symbols: hasheq from chunk name to placement
(struct placed-image (params headers-size sections size-of-image symbols))
