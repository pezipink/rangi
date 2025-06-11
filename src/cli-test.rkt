#lang racket


(require (for-syntax "cli-reader.rkt"))
(require (for-syntax syntax/parse))
(require racket/string)
(begin-for-syntax  
  (define asms (make-hash))
  
  )



(define-syntax (add-ref stx)
  (syntax-parse stx
    [(_ f)
     #:with s (local-expand #'f 'expression #f)
     (writeln (format "compile time reading ~a" #'s))
     (define asm (read-file (syntax-e #'s)))
     (define tys (get-public-typedefs asm))
     (writeln (format "public type count ~a" (length tys)))
     (hash-set! asms (syntax-e #'f) asm)
     #''(cli-add-ref f)
     ]))


(define-syntax (test stx)
  
  ;(writeln (format "~a" asms))
  

  (if (hash-has-key? asms "c:/temp/nano.exe")
      (begin (writeln (format "~a" (hash-ref asms "c:/temp/nano.exe")))
      (syntax-property #'(writeln "t") 'type 'string))
      #'(writeln "f")))
  

;(add-ref "c:/temp/nano.exe")
;(add-ref "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/System.dll")
(add-ref "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")



;(test)

#;(time (begin
        (for ([f (directory-list "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/" #:build? #t )])
          (let ([s (path->string f)])
            (when (string-suffix? (path->string f) ".dll")
           ; (writeln (path->string f))
            ;(port->bytes (open-input-file f))
            (add-ref f)
            )))
        #t))
