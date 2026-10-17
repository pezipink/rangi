#lang racket/base
; Round trips between the signature encoders (sigs.rkt) and the reader's decoders, and the
; generics rows written by build-metadata read back through read-row (ECMA-335 II.23.2, II.22.20,
; II.22.21, II.22.29).
(require rackunit
         "../../src/cli/sigs.rkt"
         "../../src/cli/reader.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/lower.rkt"
         "../../src/pe/model.rkt")

(test-case "type descriptors survive encode then decode, including 2-byte coded indexes"
  (define types
    (list 'int32
          'string
          'typedref
          '(szarray (byref int32))
          '(ptr void)
          '(class (typedef . 1))
          '(valuetype (typeref . 200))
          '(class (typespec . 300))
          '(genericinst (class (typeref . 1)) (int32 (var 0) (mvar 300)
                                                     (genericinst (valuetype (typedef . 2)) (string))))))
  (for ([t (in-list types)])
    (check-equal? (decode-typespec (encode-typespec t)) t)))

(test-case "method signatures round trip with generic arity and a 2-byte parameter count"
  (define params (for/list ([i (in-range 130)]) 'int32))
  (check-equal? (decode-method-sig (encode-method-sig 'void params #:hasthis? #t #:generic-arity 200))
                (method-signature #t #f 200 'void params))
  (check-equal? (decode-method-sig
                 (encode-method-sig '(class (typeref . 1)) '(string) #:explicitthis? #t))
                (method-signature #f #t 0 '(class (typeref . 1)) '(string))))

(test-case "LocalVarSig and MethodSpec instantiation blobs round trip"
  (define locals '(int32 (pinned (szarray string)) (byref (var 0)) typedref))
  (check-equal? (decode-localvar-sig (encode-localvar-sig locals)) locals)
  (define args (list 'int32 '(class (typedef . 5))))
  (check-equal? (decode-method-instantiation (encode-method-instantiation args)) args))

(test-case "decoders reject trailing bytes, truncation, and signatures the encoders never write"
  (check-exn exn:fail? (λ () (decode-typespec (bytes #x08 #x00))))
  (check-exn exn:fail? (λ () (decode-typespec (bytes #x1D))))
  ; TypeDefOrRefOrSpec tag 3 is unused: (1 << 2) | 3 = 7
  (check-exn exn:fail? (λ () (decode-typespec (bytes #x12 #x07))))
  ; VARARG calling convention
  (check-exn exn:fail? (λ () (decode-method-sig (bytes #x05 #x00 #x01))))
  ; GENERIC with zero generic parameters
  (check-exn exn:fail? (λ () (decode-method-sig (bytes #x10 #x00 #x00 #x01))))
  ; LocalVarSig must start with LOCAL_SIG (0x07)
  (check-exn exn:fail? (λ () (decode-localvar-sig (bytes #x06 #x00))))
  ; a MethodSpec needs at least one argument
  (check-exn exn:fail? (λ () (decode-method-instantiation (bytes #x0A #x00)))))

(define method-sig (encode-method-sig 'void '(int32) #:hasthis? #t))
(define memberref-sig (encode-method-sig 'int32 '(string) #:generic-arity 1))

(define program
  (cli-program '(("mscorlib" (4 0 0 0) #""))
               (list (list 1 "System" "Object"))
               (list (list (cons 'typeref 1) "Foo" memberref-sig))
               '()
               '()
               '()
               (list (tdef 1 "C" "N" #f (list (mdef "M" 1 method-sig #f #f)) '() #f))
               "rangi.dll"
               0
               #f
               '()
               #f
               'console
               'anycpu
               '()
               '()
               '()))

(test-case "InterfaceImpl rows read back with the class and the typedeforref interface"
  (define p (struct-copy cli-program program
                         [interfaceimpls (list (interfaceimpl 1 (cons 'typeref 1)))]))
  (define rdr
    (read-metadata-root (chunk-bytes (build-metadata p "rangi-test" "rangi.dll"))))
  (define ii (read-row rdr 'interfaceimpl 1))
  (check-equal? (vector-ref ii 0) 1)
  (check-equal? (vector-ref ii 1) (cons 'typeref 1)))

(define (add-generics-rows! tb sh bh)
  (add-typespec-row! tb bh (encode-typespec '(genericinst (class (typeref . 1)) (int32 (var 0)))))
  (add-standalonesig-row! tb bh (encode-localvar-sig '(int32 (pinned (szarray string)) (byref (var 0)) typedref)))
  (add-methodspec-row! tb bh (cons 'methoddef 1) (encode-method-instantiation '(int32 string)))
  (add-methodspec-row! tb bh (cons 'memberref 1) (encode-method-instantiation (list '(class (typedef . 1)))))
  ; owners: typedef 1 (typeormethoddef tag 0) and methoddef 1 (tag 1); inserted in sorted order
  (define gp-t (add-genericparam-row! tb sh 0 0 (cons 'typedef 1) "T"))
  (define gp-u (add-genericparam-row! tb sh 1 0 (cons 'methoddef 1) "U"))
  (add-genericparamconstraint-row! tb gp-t (cons 'typeref 1))
  (add-genericparamconstraint-row! tb gp-u (cons 'typedef 1)))

(test-case "generics and signature rows read back through read-row from bare metadata-root bytes"
  (define rdr
    (read-metadata-root
     (chunk-bytes (build-metadata program "rangi-test" "rangi.dll" #:extra add-generics-rows!))))
  (check-equal? (decode-typespec (vector-ref (read-row rdr 'typespec 1) 0))
                '(genericinst (class (typeref . 1)) (int32 (var 0))))
  (check-equal? (decode-localvar-sig (vector-ref (read-row rdr 'standalonesig 1) 0))
                '(int32 (pinned (szarray string)) (byref (var 0)) typedref))
  (define ms1 (read-row rdr 'methodspec 1))
  (check-equal? (vector-ref ms1 0) (cons 'methoddef 1))
  (check-equal? (decode-method-instantiation (vector-ref ms1 1)) '(int32 string))
  (define ms2 (read-row rdr 'methodspec 2))
  (check-equal? (vector-ref ms2 0) (cons 'memberref 1))
  (check-equal? (decode-method-instantiation (vector-ref ms2 1)) '((class (typedef . 1))))
  (define gp1 (read-row rdr 'genericparam 1))
  (check-equal? (vector-ref gp1 0) 0)
  (check-equal? (vector-ref gp1 2) (cons 'typedef 1))
  (check-equal? (vector-ref gp1 3) "T")
  (define gp2 (read-row rdr 'genericparam 2))
  (check-equal? (vector-ref gp2 0) 1)
  (check-equal? (vector-ref gp2 2) (cons 'methoddef 1))
  (check-equal? (vector-ref gp2 3) "U")
  (check-equal? (vector-ref (read-row rdr 'genericparamconstraint 1) 0) 1)
  (check-equal? (vector-ref (read-row rdr 'genericparamconstraint 1) 1) (cons 'typeref 1))
  (check-equal? (vector-ref (read-row rdr 'genericparamconstraint 2) 0) 2)
  (check-equal? (vector-ref (read-row rdr 'genericparamconstraint 2) 1) (cons 'typedef 1))
  (define md (read-row rdr 'methoddef 1))
  (check-equal? (vector-ref md 3) "M")
  (check-equal? (decode-method-sig (vector-ref md 4)) (method-signature #t #f 0 'void '(int32)))
  (define mr (read-row rdr 'memberref 1))
  (check-equal? (vector-ref mr 1) "Foo")
  (check-equal? (decode-method-sig (vector-ref mr 2))
                (method-signature #f #f 1 'int32 '(string))))
