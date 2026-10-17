#lang racket/base
;; Label resolution and branch relaxation for CIL instruction sequences.
;;
;; Input items:
;;   name:             defines label `name`
;;   (label name)      same as above
;;   op                instruction without operand
;;   (op arg)          instruction with one operand; branch targets are label symbols
;;   (switch t ...)    switch with label targets
;; Branches start in their short form and are promoted to the long form when
;; the displacement does not fit in int8. Promotion only grows code, so the
;; loop reaches a fixed point, and the result depends only on the input order.
;; A user-written `X.s` is never promoted; it is an error if it does not fit.
;; Displacements are measured from the end of the branch instruction. Switch
;; offsets are measured from the end of the whole switch.

(require "opcodes.rkt" "encode.rkt")

(provide (struct-out assembly)
         assemble-items
         assembly-label-offset)

;; code: bytes. labels: alist of (name . byte offset), in definition order.
(struct assembly (code labels) #:transparent)

(struct lab (name))
(struct fixed (bytes))
;; short: opcode for the short form or #f; long: opcode for the long form or #f.
(struct br (name short long target forced?))
(struct sw (targets))

(define (label-symbol? s)
  (define str (symbol->string s))
  (and (> (string-length str) 1)
       (char=? (string-ref str (sub1 (string-length str))) #\:)))

(define (label-name-of s)
  (define str (symbol->string s))
  (string->symbol (substring str 0 (sub1 (string-length str)))))

(define (check-target t)
  (unless (symbol? t)
    (error 'assemble-items "branch target must be a label name, got ~e" t))
  t)

(define (single-arg name args)
  (cond
    [(null? args) #f]
    [(null? (cdr args)) (car args)]
    [else (error 'assemble-items "~a takes one operand, got ~e" name args)]))

;; Short form of a long branch: `X` pairs with `X.s` (III.3.x branch table).
(define (short-form-of op)
  (define short (find-opcode (string->symbol (string-append (symbol->string (opcode-name op)) ".s"))))
  (and short (eq? (opcode-operand short) 'ShortInlineBrTarget) short))

(define (parse-instruction name args)
  (define op (opcode-named name))
  (case (opcode-operand op)
    [(ShortInlineBrTarget)
     (br name op #f (check-target (single-arg name args)) #t)]
    [(InlineBrTarget)
     (br name (short-form-of op) op (check-target (single-arg name args)) #f)]
    [(InlineSwitch)
     (sw (map check-target args))]
    [else
     (fixed (encode-instruction name (single-arg name args)))]))

(define (parse-item item)
  (cond
    [(and (symbol? item) (label-symbol? item)) (lab (label-name-of item))]
    [(and (pair? item) (eq? (car item) 'label) (pair? (cdr item)))
     (lab (check-target (cadr item)))]
    [(symbol? item) (parse-instruction item '())]
    [(and (pair? item) (symbol? (car item)))
     (parse-instruction (car item) (cdr item))]
    [else (error 'assemble-items "bad item: ~e" item)]))

;; Initial form: long only when there is no short form.
(define (initially-long? e)
  (and (br? e) (not (br-forced? e)) (not (br-short e))))

(define (entry-length e long?)
  (cond
    [(lab? e) 0]
    [(fixed? e) (bytes-length (fixed-bytes e))]
    [(br? e) (if long?
                 (+ (opcode-size (br-long e)) 4)
                 (+ (opcode-size (br-short e)) 1))]
    [(sw? e) (switch-instruction-length (length (sw-targets e)))]))

;; Start offset of each entry for the current forms.
(define (compute-offsets entries forms)
  (define n (vector-length entries))
  (define offs (make-vector n 0))
  (for/fold ([pos 0]) ([i (in-range n)])
    (vector-set! offs i pos)
    (+ pos (entry-length (vector-ref entries i) (vector-ref forms i))))
  offs)

(define (fits-int8? d) (<= -128 d 127))

(define (assemble-items items)
  (define entries (for/vector ([item (in-list items)]) (parse-item item)))
  (define n (vector-length entries))
  ;; Label name -> entry index. Lookup only; output order follows `entries`.
  (define defined (make-hasheq))
  (for ([e (in-vector entries)] [i (in-naturals)] #:when (lab? e))
    (when (hash-ref defined (lab-name e) #f)
      (error 'assemble-items "duplicate label: ~a" (lab-name e)))
    (hash-set! defined (lab-name e) i))
  (for ([e (in-vector entries)])
    (define targets
      (cond [(br? e) (list (br-target e))]
            [(sw? e) (sw-targets e)]
            [else '()]))
    (for ([t (in-list targets)])
      (unless (hash-ref defined t #f)
        (error 'assemble-items "undefined label: ~a" t))))

  (define forms (for/vector #:length n ([e (in-vector entries)]) (initially-long? e)))
  (define (target-index t) (hash-ref defined t))

  ;; Promote until no short branch needs to grow.
  (let relax ()
    (define offs (compute-offsets entries forms))
    (define changed? #f)
    (for ([e (in-vector entries)] [i (in-naturals)])
      (when (and (br? e) (not (vector-ref forms i)) (not (br-forced? e)))
        (define end (+ (vector-ref offs i) (entry-length e #f)))
        (define d (- (vector-ref offs (target-index (br-target e))) end))
        (unless (fits-int8? d)
          (vector-set! forms i #t)
          (set! changed? #t))))
    (when changed? (relax)))

  (define offs (compute-offsets entries forms))
  (define (displacement i t len)
    (- (vector-ref offs (target-index t)) (+ (vector-ref offs i) len)))

  (define code-parts
    (for/list ([e (in-vector entries)] [i (in-naturals)])
      (define long? (vector-ref forms i))
      (cond
        [(lab? e) #""]
        [(fixed? e) (fixed-bytes e)]
        [(br? e)
         (define len (entry-length e long?))
         (define d (displacement i (br-target e) len))
         (cond
           [long? (bytes-append (opcode-bytes (br-long e)) (encode-int32 d))]
           [else
            (unless (fits-int8? d)
              (error 'assemble-items "short branch ~a to ~a: displacement ~a does not fit in int8"
                     (br-name e) (br-target e) d))
            (bytes-append (opcode-bytes (br-short e)) (encode-int8 d))])]
        [(sw? e)
         (define end (+ (vector-ref offs i) (entry-length e #f)))
         (define ds (for/list ([t (in-list (sw-targets e))])
                      (- (vector-ref offs (target-index t)) end)))
         (encode-instruction 'switch ds)])))

  (define labels
    (for/list ([e (in-vector entries)] [i (in-naturals)] #:when (lab? e))
      (cons (lab-name e) (vector-ref offs i))))

  (assembly (apply bytes-append code-parts) labels))

(define (assembly-label-offset asm name)
  (define p (assq name (assembly-labels asm)))
  (unless p (error 'assembly-label-offset "no label named ~a" name))
  (cdr p))
