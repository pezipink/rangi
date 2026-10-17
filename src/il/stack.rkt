#lang racket/base
;; Maximum evaluation-stack depth by abstract interpretation over the control-flow
;; graph. Depths are counted in items. Pop and push counts come from the
;; Reflection.Emit stack behaviours in opcodes.rkt. Call-like instructions have
;; signature-dependent counts, so the caller supplies their effects.

(require "opcodes.rkt")

(provide (struct-out label-at)
         (struct-out effect)
         compute-max-stack
         opcode-pop-count
         opcode-push-count
         opcode-flow-kind)

;; A label definition in the instruction sequence.
(struct label-at (name))

;; One instruction. flow is one of:
;;   'next    falls through
;;   'branch  unconditional, no fallthrough; targets get the depth after the pops
;;   'cond    falls through and jumps to targets (also switch)
;;   'leave   jumps to targets with an empty stack (III.3.46)
;;   'return  ret; the stack must be empty after the pops
;;   'throw   no successor
(struct effect (name pop push flow targets))

(define pop-counts
  (hasheq 'Pop0 0 'Pop1 1 'Pop1_pop1 2 'Popi 1 'Popi_pop1 2 'Popi_popi 2
          'Popi_popi_popi 3 'Popi_popi8 2 'Popi_popr4 2 'Popi_popr8 2
          'Popref 1 'Popref_pop1 2 'Popref_popi 2 'Popref_popi_pop1 3
          'Popref_popi_popi 3 'Popref_popi_popi8 3 'Popref_popi_popr4 3
          'Popref_popi_popr8 3 'Popref_popi_popref 3))

(define push-counts
  (hasheq 'Push0 0 'Push1 1 'Push1_push1 2 'Pushi 1 'Pushi8 1 'Pushr4 1
          'Pushr8 1 'Pushref 1))

; Varpop and Varpush depend on the callee signature, so they are rejected here.
(define (opcode-pop-count op)
  (or (hash-ref pop-counts (opcode-pop op) #f)
      (error 'rangi "instruction ~a has a signature-dependent pop count" (opcode-name op))))

(define (opcode-push-count op)
  (or (hash-ref push-counts (opcode-push op) #f)
      (error 'rangi "instruction ~a has a signature-dependent push count" (opcode-name op))))

(define (opcode-flow-kind op)
  (case (opcode-name op)
    [(leave leave.s) 'leave]
    [else
     (case (opcode-flow op)
       [(Next Call Break Meta) 'next]
       [(Branch) 'branch]
       [(Cond_Branch) 'cond]
       [(Return) 'return]
       [(Throw) 'throw]
       [else (error 'rangi "unknown flow kind ~a" (opcode-flow op))])]))

; entries: label-at and effect values in program order.
; handlers: (label-name . depth) pairs. Each handler entry starts with the given depth,
; for example 1 for a catch handler that receives the exception object.
(define (compute-max-stack entries #:handlers [handlers '()])
  (define v (list->vector entries))
  (define n (vector-length v))
  (define index (make-hasheq))
  (for ([e (in-vector v)] [i (in-naturals)] #:when (label-at? e))
    (when (hash-ref index (label-at-name e) #f)
      (error 'rangi "duplicate label ~a" (label-at-name e)))
    (hash-set! index (label-at-name e) i))
  (define (target-index name)
    (or (hash-ref index name #f) (error 'rangi "undefined label ~a" name)))
  (define (describe i)
    (define e (vector-ref v i))
    (if (label-at? e)
        (format "label ~a" (label-at-name e))
        (format "instruction ~a (item ~a)" (effect-name e) i)))

  (define depth (make-vector n #f))
  (define max-depth 0)
  (define work '())

  ; Records that control reaches item i with depth d. Unvisited items are queued;
  ; a visited item must have the same depth on every path.
  (define (reach! i d from)
    (cond
      [(>= i n)
       (error 'rangi "control falls off the end of the method after ~a" from)]
      [(vector-ref depth i)
       => (lambda (old)
            (unless (= old d)
              (error 'rangi "stack depth mismatch at ~a: ~a items from ~a, ~a items from another path"
                     (describe i) old from d)))]
      [else
       (vector-set! depth i d)
       (set! max-depth (max max-depth d))
       (set! work (cons i work))]))

  (for ([h (in-list handlers)])
    (reach! (target-index (car h)) (cdr h) (format "handler ~a" (car h))))
  (when (> n 0) (reach! 0 0 "method entry"))

  (let loop ()
    (unless (null? work)
      (define i (car work))
      (set! work (cdr work))
      (define d (vector-ref depth i))
      (define e (vector-ref v i))
      (cond
        [(label-at? e) (reach! (add1 i) d (describe i))]
        [else
         (define pop (effect-pop e))
         (when (> pop d)
           (error 'rangi "stack underflow at ~a: needs ~a items, depth is ~a"
                  (describe i) pop d))
         (define d2 (+ (- d pop) (effect-push e)))
         (set! max-depth (max max-depth d2))
         (define from (describe i))
         (case (effect-flow e)
           [(next) (reach! (add1 i) d2 from)]
           [(branch) (for ([t (in-list (effect-targets e))])
                       (reach! (target-index t) d2 from))]
           [(cond)
            (reach! (add1 i) d2 from)
            (for ([t (in-list (effect-targets e))])
              (reach! (target-index t) d2 from))]
           [(leave)
            (for ([t (in-list (effect-targets e))])
              (reach! (target-index t) 0 from))]
           [(return)
            (unless (zero? d2)
              (error 'rangi "~a leaves ~a extra items on the stack" from d2))]
           [(throw) (void)]
           [else (error 'rangi "unknown flow ~a" (effect-flow e))])])
      (loop)))
  max-depth)
