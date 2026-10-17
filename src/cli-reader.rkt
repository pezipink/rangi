#lang racket/base
; compatibility shim: the reader moved to cli/reader.rkt. Remove once callers use the new path.
(require "cli/reader.rkt")
(provide (all-from-out "cli/reader.rkt"))
