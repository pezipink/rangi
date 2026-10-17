#lang racket/base
; Exception clauses (II.25.4.6). finally and fault clauses carry Flags 0x0002 and 0x0004 and
; ClassToken 0. Each handler starts with its entry stack depth: a catch starts with the
; exception object (1 item), a finally or fault starts with 0 (III.1.7.5).
(require rackunit racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt")

(define mscorlib-ref
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; Lowers a one-method module whose main body is the given forms and returns main's body bytes.
(define (main-body . forms)
  (define prog
    (lower-module
     (parse-il
      `((.assembly extern ,mscorlib-ref {})
        (.assembly donothing {})
        (.module local.exe)
        (.class (private auto ansi) <Module>
          [(.method (public static) void main () (cil managed)
             { (.entrypoint) ,@forms (ret) })])))))
  (mdef-body (findf (λ (m) (equal? (mdef-name m) "main"))
                    (append-map tdef-methods (cli-program-typedefs prog)))))

(define (u32 bs p) (integer-bytes->integer bs #f #f p (+ p 4)))

; The code bytes of a fat method body (II.25.4.3).
(define (code-of body)
  (subbytes body 12 (+ 12 (u32 body 4))))

; The clauses of the fat EH section (II.25.4.5, II.25.4.6), each as a list of six u32 fields:
; (flags try-start try-length handler-start handler-length class-token).
(define (eh-clauses body)
  (define code-size (u32 body 4))
  (define sec (+ 12 code-size (modulo (- 4 (modulo code-size 4)) 4)))
  (check-equal? (bytes-ref body sec) #x41 "Kind byte is EHTable | FatFormat")
  (define size (+ (bytes-ref body (+ sec 1))
                  (* 256 (bytes-ref body (+ sec 2)))
                  (* 65536 (bytes-ref body (+ sec 3)))))
  (for/list ([i (in-range (quotient (- size 4) 24))])
    (define p (+ sec 4 (* 24 i)))
    (for/list ([k (in-range 6)]) (u32 body (+ p (* 4 k))))))

(test-case "a finally clause has flags 0x0002, ClassToken 0, and a handler ending in endfinally"
  (define body
    (main-body
     '(.maxstack 8)
     '(.try (finally) ts te hs he)
     'ts: '(ldc.i4.1) '(pop) '(leave done)
     'te: 'hs: '(ldc.i4.1) '(pop) 'endfinally
     'he: 'done:))
  (define clauses (eh-clauses body))
  (check-equal? (length clauses) 1)
  (define-values (flags ts tlen hs hlen tok) (apply values (first clauses)))
  (check-equal? flags #x0002 "finally flag")
  (check-equal? tok 0 "finally ClassToken is 0")
  (check-equal? (+ ts tlen) hs "the handler starts where the protected region ends")
  (check-equal? (bytes-ref (code-of body) (+ hs hlen -1)) #xDC "handler ends with endfinally"))

(test-case "a fault clause has flags 0x0004 and ClassToken 0, and (endfault) encodes as 0xDC"
  (define body
    (main-body
     '(.maxstack 8)
     '(.try (fault) fts fte fhs fhe)
     'fts: '(ldc.i4.1) '(pop) '(leave after)
     'fte: 'fhs: '(ldc.i4.2) '(pop) '(endfault)
     'fhe: 'after:))
  (define clauses (eh-clauses body))
  (define-values (flags ts tlen hs hlen tok) (apply values (first clauses)))
  (check-equal? flags #x0004 "fault flag")
  (check-equal? tok 0 "fault ClassToken is 0")
  (check-equal? (bytes-ref (code-of body) (+ hs hlen -1)) #xDC "(endfault) encodes as 0xDC"))

(test-case "a bare endfault next to a catch: fault first, catch keeps its TypeRef token"
  (define body
    (main-body
     '(.maxstack 8)
     '(.try (fault) fts fte fhs fhe)
     '(.try (catch (mscorlib System.Exception)) cts cte chs che)
     'fts: '(ldc.i4.1) '(pop) '(leave after)
     'fte: 'fhs: '(ldc.i4.2) '(pop) 'endfault
     'fhe: 'cts: '(ldc.i4.3) '(pop) '(leave after)
     'cte: 'chs: '(pop) '(ldc.i4.4) '(pop) '(leave after)
     'che: 'after:))
  (define clauses (eh-clauses body))
  (check-equal? (map first clauses) '(#x0004 #x0000) "fault then catch, in source order")
  (check-equal? (bitwise-and (sixth (second clauses)) #xFF000000) #x01000000
                "catch ClassToken is a TypeRef token"))

; Handler entry depth. The handler body pushes 1 then 2 and pops them. A catch starts with the
; exception object, so it peaks at 3 and must pop that too. A finally or fault starts empty and
; peaks at 2. An explicit .maxstack below the computed depth is an error, so the error message
; shows which depth the lowering used.
(define (handler-program kind maxstack)
  (append
   (list `(.maxstack ,maxstack)
         (if (eq? kind 'catch)
             '(.try (catch (mscorlib System.Exception)) ts te hs he)
             (list '.try (list kind) 'ts 'te 'hs 'he)))
   '(ts: (ldc.i4.1) (pop) (leave done)
     te: hs: (ldc.i4.1) (ldc.i4.2) (pop) (pop))
   (case kind
     [(catch) '((pop) (leave done))]
     [(finally) '(endfinally)]
     [(fault) '(endfault)])
   '(he: done:)))

(test-case "a catch handler starts with depth 1, so its body peaks at 3"
  (check-exn #rx"computed maximum stack depth 3"
             (λ () (apply main-body (handler-program 'catch 2))))
  (check-not-exn (λ () (apply main-body (handler-program 'catch 3)))))

(test-case "a finally handler starts with depth 0, so its body peaks at 2"
  (check-exn #rx"computed maximum stack depth 2"
             (λ () (apply main-body (handler-program 'finally 1))))
  (check-not-exn (λ () (apply main-body (handler-program 'finally 2)))))

(test-case "a fault handler starts with depth 0, so its body peaks at 2"
  (check-exn #rx"computed maximum stack depth 2"
             (λ () (apply main-body (handler-program 'fault 1))))
  (check-not-exn (λ () (apply main-body (handler-program 'fault 2)))))

(test-case "filter clauses are rejected as unsupported"
  (check-exn #rx"malformed .try"
             (λ ()
               (parse-il
                `((.assembly extern ,mscorlib-ref {})
                  (.module local.exe)
                  (.class (private auto ansi) <Module>
                    [(.method (public static) void main () (cil managed)
                       { (.entrypoint) (.try (filter) a b c d) (ret) })]))))))
