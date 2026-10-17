#lang racket/base
(require rackunit
         racket/file
         racket/format
         racket/runtime-path
         racket/string
         "../src/il/opcodes.rkt")

(define-runtime-path fixture-path "fixtures/opcodes.tsv")

(define reserved-prefixes
  '("prefix1" "prefix2" "prefix3" "prefix4" "prefix5" "prefix6" "prefix7" "prefixref"))

(define no-dot-cols
  '("no." "2" "FE" "19" "ShortInlineI" "Meta" "Pop0" "Push0" "Prefix"))

(define (hex2 n)
  (string-upcase (~r n #:base 16 #:min-width 2 #:pad-string "0")))

(define (table-cols op)
  (define v (opcode-value op))
  (define two? (= (opcode-size op) 2))
  (list (symbol->string (opcode-name op))
        (number->string (opcode-size op))
        (hex2 (if two? (quotient v 256) v))
        (if two? (hex2 (remainder v 256)) "-")
        (symbol->string (opcode-operand op))
        (symbol->string (opcode-flow op))
        (symbol->string (opcode-pop op))
        (symbol->string (opcode-push op))
        (symbol->string (opcode-type op))))

(define (cols-value cols)
  (define b1 (string->number (list-ref cols 2) 16))
  (if (equal? (list-ref cols 3) "-")
      b1
      (+ (* 256 b1) (string->number (list-ref cols 3) 16))))

(define fixture-rows
  (for/list ([line (in-list (file->lines fixture-path))])
    (string-split line "\t" #:trim? #f)))

(define expected-rows
  (sort (cons no-dot-cols
              (for/list ([cols (in-list fixture-rows)]
                         #:unless (member (car cols) reserved-prefixes))
                cols))
        <
        #:key cols-value))

(test-case "fixture lists every Reflection.Emit opcode"
  (check-equal? (length fixture-rows) 226))

(test-case "table has one entry per non-prefix opcode plus no."
  (check-equal? (length opcode-table) 219))

(test-case "table values are strictly increasing"
  (define vs (map opcode-value opcode-table))
  (check-true (for/and ([a (in-list vs)] [b (in-list (cdr vs))]) (< a b))))

(test-case "table equals fixture minus reserved prefixes plus no."
  (check-equal? (map table-cols opcode-table) expected-rows))
