#lang racket/base
; The CLI header (II.25.3.3) as a chunk. The MetaData RVA is a fixup to the metadata chunk.
(require "../pe/model.rkt"
         "../private/binary.rkt")
(provide cli-header-chunk
         cli-flag-ilonly)

; COMIMAGE_FLAGS_ILONLY (II.25.3.3.1)
(define cli-flag-ilonly #x1)

; metadata-size is the byte length of the metadata chunk. entry-rid is the MethodDef
; row of the entry point, which the entry token names (II.22.22). A DLL with no entry point
; passes #f, and the token is 0 (II.25.3.3).
(define (cli-header-chunk #:metadata-size metadata-size
                          #:entry-rid entry-rid
                          #:flags [flags cli-flag-ilonly])
  (chunk 'cli-header 4
         (bytes-append (le #x48 4) (le 2 2) (le 0 2)
                       (make-bytes 4 0) (le metadata-size 4)
                       (le flags 4)
                       (le (if entry-rid (bitwise-ior #x06000000 entry-rid) 0) 4)
                       (make-bytes 48 0))
         (list (fixup 8 'rva32 'metadata))))
