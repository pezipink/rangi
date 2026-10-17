#lang racket/base
; Array types in the ilasm front end. (szarray T) is the SZARRAY form of T[] (II.23.2.12),
; used because Racket reads [ and ] as delimiters. Element types are checked by check-type.
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

(test-case "a szarray parameter and a szarray return parse as nested types"
  (define m (parse-il (program (method '(szarray int32) '((szarray int32)) '((ldarg.0) (ret))
                                       #:name 'helper)
                               (method 'void '() entry-il))))
  (define h (method-named m 'helper))
  (check-equal? (method-decl-ret h) '(szarray int32))
  (check-equal? (method-decl-params h) '((szarray int32))))

(test-case "a szarray of szarray parses (jagged array element)"
  (define m (parse-il (program (method 'void '((szarray (szarray int32))) entry-il))))
  (check-equal? (method-decl-params (method-named m 'main)) '((szarray (szarray int32)))))

(test-case "a szarray of a class type parses"
  (define m (parse-il (program (method 'void '((szarray (class Foo))) entry-il))))
  (check-equal? (method-decl-params (method-named m 'main)) '((szarray (class Foo)))))

(test-case "a szarray local parses as a bare type and as a named local"
  (define m (parse-il (program (method 'void '() entry-il
                                       #:locals '((szarray int32) ((szarray int64) arr))))))
  (check-equal? (method-decl-locals (method-named m 'main))
                (locals-decl #t (list (local-var '(szarray int32) #f)
                                      (local-var '(szarray int64) 'arr)))))

(test-case "a szarray of void is rejected"
  (check-exn #rx"array element type cannot be void"
             (λ () (parse-il (program (method 'void '((szarray void)) entry-il))))))

(test-case "a szarray of typedref is rejected"
  (check-exn #rx"array element type cannot be typedref"
             (λ () (parse-il (program (method 'void '((szarray typedref)) entry-il))))))
