#lang racket/base
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt")

; One method with a .entrypoint, the only shape the front end needs for these checks.
(define (method ret params il #:mtp [mtp #f])
  (if mtp
      (list '.method '(public static) ret 'main mtp params '(cil managed) il)
      (list '.method '(public static) ret 'main params '(cil managed) il)))

(define (program #:ctp [ctp #f] . methods)
  (list (if ctp
            (list '.class '() 'Program ctp methods)
            (list '.class '() 'Program methods))))

(define (program-class m)
  (findf (lambda (c) (eq? (class-decl-name c) 'Program)) (module-model-classes m)))

(define (entry-method m)
  (findf method-decl-entry? (class-decl-methods (program-class m))))

(define entry-il '((.entrypoint) (ret)))

(test-case "class type parameters with specials and constraints"
  (define ctp '(.typarams T (U class (class Foo)) (V (class Bar (int32 !0))) (W !0)))
  (define m (parse-il (program #:ctp ctp (method 'void '() entry-il))))
  (check-equal? (class-decl-gparams (program-class m))
                (list (generic-param 'T '() '())
                      (generic-param 'U '(class) '((class Foo)))
                      (generic-param 'V '() '((class Bar (int32 !0))))
                      (generic-param 'W '() '(!0)))))

(test-case "method type parameter used in the return type and parameters"
  (define m (parse-il (program (method '!!0 '(!!0) entry-il #:mtp '(.typarams M)))))
  (define e (entry-method m))
  (check-equal? (method-decl-gparams e) (list (generic-param 'M '() '())))
  (check-equal? (method-decl-ret e) '!!0)
  (check-equal? (method-decl-params e) '(!!0))
  (check-equal? (method-decl-code e) '((ret)))
  (check-true (method-decl-entry? e)))

(test-case "generic class type argument with a class variable"
  (define m (parse-il (program #:ctp '(.typarams T)
                               (method 'void '((class Foo (int32 !0))) entry-il))))
  (check-equal? (method-decl-params (entry-method m)) '((class Foo (int32 !0)))))

(test-case ".locals init with named, bare and generic entries"
  (define m (parse-il (program #:ctp '(.typarams T)
                               (method 'void '()
                                       '((.locals init (int32 (int32 count) (class Foo)
                                                              (class Foo (int32 !0))))
                                         (.entrypoint) (ret))))))
  (check-equal? (method-decl-locals (entry-method m))
                (locals-decl #t (list (local-var 'int32 #f)
                                      (local-var 'int32 'count)
                                      (local-var '(class Foo) #f)
                                      (local-var '(class Foo (int32 !0)) #f)))))

(test-case "plain .locals without init"
  (define m (parse-il (program (method 'void '()
                                       '((.locals ((int32 x)))
                                         (.entrypoint) (ret))))))
  (check-equal? (method-decl-locals (entry-method m))
                (locals-decl #f (list (local-var 'int32 'x)))))

(test-case "legacy shapes have no generic parameters and no locals"
  (define m (parse-il (program (method 'void '() entry-il))))
  (check-equal? (class-decl-gparams (program-class m)) '())
  (check-equal? (method-decl-gparams (entry-method m)) '())
  (check-false (method-decl-locals (entry-method m))))

(test-case "generic syntax errors"
  (check-exn #rx"duplicate .locals"
             (lambda ()
               (parse-il (program (method 'void '()
                                          '((.locals (int32)) (.locals (int32))
                                            (.entrypoint) (ret)))))))
  (check-exn #rx"duplicate local"
             (lambda ()
               (parse-il (program (method 'void '()
                                          '((.locals ((int32 x) (int32 x))) (.entrypoint) (ret)))))))
  (check-exn #rx"unknown type"
             (lambda () (parse-il (program (method 'frob '() entry-il)))))
  (check-exn #rx"out of range"
             (lambda ()
               (parse-il (program (method 'void '(!!1) entry-il
                                          #:mtp '(.typarams M))))))
  (check-exn #rx"out of range"
             (lambda () (parse-il (program (method 'void '(!0) entry-il)))))
  (check-exn #rx"empty generic argument list"
             (lambda () (parse-il (program (method 'void '((class Foo ())) entry-il)))))
  (check-exn #rx"duplicate generic parameter"
             (lambda () (parse-il (program #:ctp '(.typarams T T) (method 'void '() entry-il)))))
  (check-exn #rx"invalid constraint"
             (lambda ()
               (parse-il (program #:ctp '(.typarams (U int32)) (method 'void '() entry-il))))))
