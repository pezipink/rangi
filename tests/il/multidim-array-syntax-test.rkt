#lang racket/base
; Multi-dimensional array types in the ilasm front end: (array ELEM RANK), where RANK is a
; positive integer and ELEM is a checked type (II.14.2, II.23.2.13).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt")

(define entry-il '((.entrypoint) (ret)))

(define (program . methods)
  (list (list '.class '() 'Program methods)))

(define (method ret params il #:name [name 'main] #:locals [locals #f])
  (define body (if locals (cons (list '.locals 'init locals) il) il))
  (list '.method '(public static) ret name params '(cil managed) body))

(define (program-class m)
  (findf (lambda (c) (eq? (class-decl-name c) 'Program)) (module-model-classes m)))

(define (method-named m name)
  (findf (lambda (x) (eq? (method-decl-name x) name))
         (class-decl-methods (program-class m))))

(test-case "a rank-2 array parameter and return parse as (array ELEM RANK)"
  (define m (parse-il (program (method '(array int32 2) '((array int32 2)) '((ldarg.0) (ret))
                                       #:name 'helper)
                               (method 'void '() entry-il))))
  (define h (method-named m 'helper))
  (check-equal? (method-decl-ret h) '(array int32 2))
  (check-equal? (method-decl-params h) '((array int32 2))))

(test-case "an array of class type parses"
  (define m (parse-il (program (method 'void '((array (class Foo) 3)) entry-il))))
  (check-equal? (method-decl-params (method-named m 'main)) '((array (class Foo) 3))))

(test-case "a multi-dimensional array local parses as a bare type and as a named local"
  (define m (parse-il (program (method 'void '() entry-il
                                       #:locals '((array int32 2) ((array int64 2) arr))))))
  (check-equal? (method-decl-locals (method-named m 'main))
                (locals-decl #t (list (local-var '(array int32 2) #f)
                                      (local-var '(array int64 2) 'arr)))))

(test-case "an array of void is rejected"
  (check-exn #rx"array element type cannot be void"
             (λ () (parse-il (program (method 'void '((array void 2)) entry-il))))))

(test-case "an array of typedref is rejected"
  (check-exn #rx"array element type cannot be typedref"
             (λ () (parse-il (program (method 'void '((array typedref 2)) entry-il))))))

(test-case "a rank of zero is rejected"
  (check-exn #rx"positive rank"
             (λ () (parse-il (program (method 'void '((array int32 0)) entry-il))))))

(test-case "a bounded array form is rejected with a clear error"
  (check-exn #rx"bounded arrays are not supported"
             (λ () (parse-il (program (method 'void '((array int32 2 (1) (0))) entry-il))))))
