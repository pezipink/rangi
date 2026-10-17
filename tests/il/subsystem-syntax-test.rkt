#lang racket/base
; .subsystem and .platform directives: accepted names, defaults, and rejected names.
(require rackunit
         "../../src/ilasm/syntax.rkt")

(define entry-class
  '(.class () Program
     ((.method (public static) void main () (cil managed) ((.entrypoint) (ret))))))

(define (module-with . directives)
  (parse-il (append directives (list entry-class))))

(test-case "defaults are console and anycpu"
  (define m (module-with))
  (check-equal? (module-model-subsystem m) 'console)
  (check-equal? (module-model-platform m) 'anycpu))

(test-case "accepted subsystem names"
  (check-equal? (module-model-subsystem (module-with '(.subsystem console))) 'console)
  (check-equal? (module-model-subsystem (module-with '(.subsystem windows))) 'windows))

(test-case "accepted platform names"
  (check-equal? (module-model-platform (module-with '(.platform anycpu))) 'anycpu)
  (check-equal? (module-model-platform (module-with '(.platform x86))) 'x86)
  (check-equal? (module-model-platform (module-with '(.platform 32bitpreferred))) '32bitpreferred))

(test-case "subsystem and platform directives are independent of the format directive"
  (define m (module-with '(.format pe32+) '(.subsystem windows) '(.platform x86)))
  (check-equal? (module-model-format m) 'pe32+)
  (check-equal? (module-model-subsystem m) 'windows)
  (check-equal? (module-model-platform m) 'x86))

(test-case "unknown subsystem names are rejected"
  (check-exn #rx"unknown .subsystem" (lambda () (module-with '(.subsystem native))))
  (check-exn #rx"unknown .subsystem" (lambda () (module-with '(.subsystem gui))))
  (check-exn #rx"unknown .subsystem" (lambda () (module-with '(.subsystem "windows")))))

(test-case "unknown platform names are rejected"
  (check-exn #rx"unknown .platform" (lambda () (module-with '(.platform x64))))
  (check-exn #rx"unknown .platform" (lambda () (module-with '(.platform itanium))))
  (check-exn #rx"unknown .platform" (lambda () (module-with '(.platform ANYCPU)))))

(test-case "duplicate subsystem and platform directives are rejected"
  (check-exn #rx"only one .subsystem"
             (lambda () (module-with '(.subsystem console) '(.subsystem windows))))
  (check-exn #rx"only one .platform"
             (lambda () (module-with '(.platform x86) '(.platform anycpu)))))
