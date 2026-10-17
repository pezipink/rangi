#lang racket/base
; The metadata root and stream headers (II.24.2.1, II.24.2.2) as a chunk. The streams are
; supplied by the caller. The MVID is a digest of the other streams (see digest in pe/model.rkt).
(require "../pe/model.rkt"
         "../private/binary.rkt")
(provide metadata-chunk)

(define runtime-version "v4.0.30319")

; streams: list of (cons name bytes), in the order their headers are written.
; table-fixups: (offset . target) pairs, with the offset relative to the start of "#~".
; mvid-index: 1-based index of the Module.Mvid entry in #GUID. The MVID is 16 bytes there.
(define (metadata-chunk streams
                        #:table-fixups [table-fixups '()]
                        #:mvid-index mvid-index)
  (define version (pad-to (bytes-append (string->bytes/utf-8 runtime-version) #"\0") 4))
  (define (stream-header name off size)
    (bytes-append (le off 4) (le size 4)
                  (pad-to (bytes-append (string->bytes/utf-8 name) #"\0") 4)))
  (define root
    (bytes-append #"BSJB" (le 1 2) (le 1 2) (le 0 4)
                  (le (bytes-length version) 4) version
                  (le 0 2) (le (length streams) 2)))
  (define header-len
    (for/sum ([st (in-list streams)]) (bytes-length (stream-header (car st) 0 0))))
  (define offsets
    (let loop ([ss streams] [off (+ (bytes-length root) header-len)] [acc '()])
      (if (null? ss)
          (reverse acc)
          (loop (cdr ss) (+ off (bytes-length (cdr (car ss)))) (cons off acc)))))
  (define headers
    (apply bytes-append
           (for/list ([st (in-list streams)] [off (in-list offsets)])
             (stream-header (car st) off (bytes-length (cdr st))))))
  (define (offset-of name)
    (for/first ([st (in-list streams)] [off (in-list offsets)] #:when (equal? (car st) name))
      off))
  (define tilde-off (offset-of "#~"))
  (define guid-off (offset-of "#GUID"))
  (define digest-spans
    (for/list ([st (in-list streams)] [off (in-list offsets)] #:unless (equal? (car st) "#GUID"))
      (cons off (+ off (bytes-length (cdr st))))))
  (chunk 'metadata 4
         (bytes-append root headers (apply bytes-append (map cdr streams)))
         (append
          (for/list ([f (in-list table-fixups)])
            (fixup (+ tilde-off (car f)) 'rva32 (cdr f)))
          (list (digest (+ guid-off (* 16 (sub1 mvid-index))) digest-spans)))))
