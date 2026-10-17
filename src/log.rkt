#lang racket/base

; debug and warning output from the reader and writer goes through this logger.
; set PLTSTDERR="warning rangi" (or "debug rangi") to see it on stderr.
(define-logger rangi)

(provide rangi-logger
         log-rangi-debug
         log-rangi-info
         log-rangi-warning
         log-rangi-error)
