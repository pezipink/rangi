#lang racket/base
; The .line directive (sequence points for the portable PDB, II.24). A .line marks the instruction
; after it. It adds no IL, so the code bytes are the same with or without it.
(require rackunit racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-ref
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; Lowers a one-method module whose main body is the given forms. The forms include their own
; final (ret), so tests can place .line directives after it.
(define (main-mdef . forms)
  (define prog
    (lower-module
     (parse-il
      `((.assembly extern ,mscorlib-ref {})
        (.assembly donothing {})
        (.module local.exe)
        (.class (private auto ansi) <Module>
          [(.method (public static) void main () (cil managed)
             { (.entrypoint) ,@forms })])))))
  (findf (λ (m) (equal? (mdef-name m) "main"))
         (append-map tdef-methods (cli-program-typedefs prog))))

(test-case "each .line becomes a sequence point at the instruction after it"
  (define d (mdef-debug (main-mdef '(.line 3 4 3 10 "a.il") '(ldc.i4.1) '(pop)
                                   '(.line 5 0 6 2 "a.il") '(ret))))
  (check-equal? (methoddebug-seqpts d)
                (list (seqpt 0 3 4 3 10 "a.il")
                      (seqpt 2 5 0 6 2 "a.il")))
  (check-equal? (methoddebug-code-size d) 3))

(test-case "a .line adds no IL bytes"
  (check-equal? (mdef-body (main-mdef '(.line 3 4 3 10 "a.il") '(ldc.i4.1) '(pop) '(ret)))
                (mdef-body (main-mdef '(ldc.i4.1) '(pop) '(ret)))))

(test-case "several .line directives at one offset keep the last, and one at the end is dropped"
  (define d (mdef-debug (main-mdef '(.line 3 4 3 10 "a.il")
                                   '(.line 7 1 7 9 "b.il")
                                   '(ldc.i4.1) '(pop) '(ret)
                                   '(.line 9 0 9 1 "a.il"))))
  (check-equal? (methoddebug-seqpts d) (list (seqpt 0 7 1 7 9 "b.il"))))

(test-case "locals keep their StandAloneSig row and the names of the named ones"
  (define d (mdef-debug (main-mdef '(.locals init ((int32 x) int32))
                                   '(.line 2 0 2 5 "a.il")
                                   '(ldc.i4.0) '(stloc.0) '(ret))))
  (check-true (> (methoddebug-locals-rid d) 0))
  (check-equal? (methoddebug-local-names d) '((0 . "x"))))

(test-case "a body-less method has no debug data"
  (define prog
    (lower-module
     (parse-il
      `((.assembly extern ,mscorlib-ref {})
        (.module local.exe)
        (.class (private auto ansi) <Module>
          [(.method (public static) void main () (cil managed) { (.entrypoint) (ret) })])
        (.class (public abstract auto ansi) Shape
          [(.method (public abstract virtual) void stub ())])))))
  (define (named n) (findf (λ (m) (equal? (mdef-name m) n))
                           (append-map tdef-methods (cli-program-typedefs prog))))
  (check-false (mdef-body (named "stub")))
  (check-false (mdef-debug (named "stub")))
  (check-true (methoddebug? (mdef-debug (named "main")))))

(test-case "a malformed or out-of-range .line is rejected"
  (check-exn #rx"hidden line"
             (λ () (main-mdef '(.line 16707566 0 16707566 1 "a.il") '(ret))))
  (check-exn #rx"line 0 is outside"
             (λ () (main-mdef '(.line 0 0 1 1 "a.il") '(ret))))
  (check-exn #rx"column 65536"
             (λ () (main-mdef '(.line 1 0 1 65536 "a.il") '(ret))))
  (check-exn #rx"end line is before"
             (λ () (main-mdef '(.line 5 0 4 0 "a.il") '(ret))))
  (check-exn #rx"end column must be after"
             (λ () (main-mdef '(.line 5 4 5 4 "a.il") '(ret))))
  (check-exn #rx"non-empty string"
             (λ () (main-mdef '(.line 1 0 1 1 "") '(ret))))
  (check-exn #rx"malformed .line"
             (λ () (main-mdef '(.line 1 0 1 "a.il") '(ret)))))
