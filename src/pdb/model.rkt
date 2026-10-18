#lang racket/base
; The debug data of a method body, as the CLI lowering produces it and the portable PDB writer
; consumes (pdb.rkt). It lives apart from both so neither depends on the other.
(provide (struct-out methoddebug)
         (struct-out seqpt))

; Debug data for one method body. code-size is the IL size, locals-rid is the StandAloneSig row of
; the locals (0 when there are none), local-names is a list of (slot . name) for each named local,
; and seqpts are the sequence points in IL offset order.
(struct methoddebug (code-size locals-rid local-names seqpts) #:transparent)
; A sequence point: the IL offset where a .line starts, its line and column span, and its file.
(struct seqpt (offset start-line start-col end-line end-col file) #:transparent)
