#lang racket/base
;; Stack depth analysis tests (ECMA-335 III.1.7.4 stack transition rules).
(require rackunit
         "../../src/il/stack.rkt"
         "../../src/il/encode.rkt")

(define (ins pop push [flow 'next] [targets '()])
  (effect 'x pop push flow targets))
(define (lbl name) (label-at name))

(define (depth entries #:handlers [handlers '()])
  (compute-max-stack entries #:handlers handlers))

;; straight-line code: push, push, add, ret
(check-equal? (depth (list (ins 0 1) (ins 0 1) (ins 2 1) (ins 1 0 'return)))
              2)
;; nothing on the stack at all
(check-equal? (depth (list (ins 0 0 'return))) 0)
;; dup pushes two items from one
(check-equal? (depth (list (ins 0 1) (ins 1 2) (ins 2 0 'return))) 2)

;; if/else: both arms leave one item at the join
(check-equal? (depth (list (ins 0 1)
                           (ins 1 0 'cond '(else))
                           (ins 0 1)
                           (ins 0 0 'branch '(end))
                           (lbl 'else)
                           (ins 0 1)
                           (lbl 'end)
                           (ins 1 0 'return)))
              1)

;; loop: the back edge carries the same depth as the loop head
(check-equal? (depth (list (lbl 'top)
                           (ins 0 1)
                           (ins 1 0 'cond '(top))
                           (ins 0 0 'return)))
              1)

;; stack grows across a back edge: mismatch at the loop head
(check-exn #rx"depth mismatch"
           (lambda () (depth (list (lbl 'top) (ins 0 1) (ins 0 0 'branch '(top))))))

;; join with depth 0 on one path and 2 on the other
(check-exn #rx"depth mismatch"
           (lambda () (depth (list (ins 0 1)
                                   (ins 1 0 'cond '(join))
                                   (ins 0 2)
                                   (lbl 'join)
                                   (ins 0 0 'return)))))

;; underflow
(check-exn #rx"stack underflow" (lambda () (depth (list (ins 2 1) (ins 1 0 'return)))))

;; falling off the end of the method
(check-exn #rx"falls off the end" (lambda () (depth (list (ins 0 1)))))

;; ret with items left over
(check-exn #rx"extra items" (lambda () (depth (list (ins 0 1) (ins 0 1) (ins 1 0 'return)))))

;; undefined and duplicate labels
(check-exn #rx"undefined label" (lambda () (depth (list (ins 0 0 'branch '(nowhere))))))
(check-exn #rx"duplicate label" (lambda () (depth (list (lbl 'a) (lbl 'a) (ins 0 0 'return)))))

;; exception handler: the handler starts with the exception object (depth 1)
(define handler-code (list (ins 0 0 'return)
                           (lbl 'handler)
                           (ins 1 0)
                           (ins 0 0 'return)))
(check-equal? (depth handler-code #:handlers '((handler . 1))) 1)
(check-equal? (depth handler-code) 0)

;; leave empties the stack at its target, so items left behind do not count against the join
(check-equal? (depth (list (ins 0 1) (ins 0 1)
                           (ins 0 0 'leave '(done))
                           (lbl 'done)
                           (ins 0 0 'return)))
              2)

;; switch: fallthrough and each target start at the depth after the index is popped
(check-equal? (depth (list (ins 0 1)
                           (ins 1 0 'cond '(a b))
                           (ins 0 0 'return)
                           (lbl 'a)
                           (ins 0 0 'return)
                           (lbl 'b)
                           (ins 0 0 'return)))
              1)

;; table-driven pop and push counts
(check-equal? (opcode-pop-count (opcode-named 'stfld)) 2)
(check-equal? (opcode-push-count (opcode-named 'dup)) 2)
(check-equal? (opcode-flow-kind (opcode-named 'leave.s)) 'leave)
(check-equal? (opcode-flow-kind (opcode-named 'brtrue)) 'cond)
(check-equal? (opcode-flow-kind (opcode-named 'br)) 'branch)
(check-exn exn:fail? (lambda () (opcode-pop-count (opcode-named 'call))))
