#lang racket/base
; Custom attributes (II.22.10): a .custom directive sits on the assembly (top level), a class (class
; body), or a method (method body). Its constructor is a MethodDef in this module or a MemberRef on an
; external attribute class, and its value is a literal blob (II.23.3) whose 0x0001 prolog is checked.
; These tests check the parse, the lowered rows, the rows as build-metadata writes them, and the errors.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/reader.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly custom-test {})
    (.module local.exe)
    (.custom (mscorlib System.ObsoleteAttribute) .ctor void (string) = (bytearray (01 00 01 78 00 00)))
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

; Marker has a same-module constructor. Widget carries a class-level attribute on an external
; constructor and a method-level attribute on Marker's constructor. (Program is the parser's holder
; for <Module> methods, so the test classes avoid that name.)
(define marker-and-widget
  '((.class (public auto ansi) Marker
      [(.method (public specialname rtspecialname) void .ctor () (cil managed) { (ret) })])
    (.class (public auto ansi) Widget
      [(.custom (mscorlib System.ObsoleteAttribute) .ctor void (string) = (bytearray (01 00 01 78 00 00)))
       (.method (public static) void Run () (cil managed)
         { (.custom Marker::.ctor void () = (bytearray (01 00 00 00))) (ret) })])))

; the 1-based rid of the method named name in the lowered program's flat MethodDef list
(define (mdef-rid-of p name)
  (define all (append* (map tdef-methods (cli-program-typedefs p))))
  (for/first ([md (in-list all)] [i (in-naturals 1)] #:when (equal? (mdef-name md) name)) i))

; the 1-based rid of the TypeDef named name
(define (tdef-rid-of p name)
  (for/first ([td (in-list (cli-program-typedefs p))] [i (in-naturals 1)]
              #:when (equal? (tdef-name td) name))
    i))

(define (class-named m name)
  (findf (λ (c) (eq? (class-decl-name c) name)) (module-model-classes m)))

(test-case "the parser keeps the parent of each .custom and its literal blob"
  (define m (parse-il (apply program marker-and-widget)))
  (check-equal? (length (module-model-customs m)) 1)
  (define asm-cu (car (module-model-customs m)))
  (check-equal? (custom-decl-ctor asm-cu) '(mscorlib System.ObsoleteAttribute))
  (check-equal? (custom-decl-params asm-cu) '(string))
  (check-equal? (custom-decl-blob asm-cu) (bytes #x01 #x00 #x01 #x78 #x00 #x00))
  (define prog (class-named m 'Widget))
  (check-equal? (length (class-decl-customs prog)) 1)
  (define run (findf (λ (md) (eq? (method-decl-name md) 'Run)) (class-decl-methods prog)))
  (check-equal? (length (method-decl-customs run)) 1)
  (check-equal? (custom-decl-ctor (car (method-decl-customs run))) 'Marker)
  (check-equal? (custom-decl-blob (car (method-decl-customs run))) (bytes #x01 #x00 #x00 #x00)))

(test-case "lowering emits CustomAttribute rows with the Parent, Type, and Value of each attribute"
  (define p (lower-module (parse-il (apply program marker-and-widget))))
  (define rows (cli-program-customattrs p))
  (check-equal? (length rows) 3)
  (define asm-row (first rows))
  (check-equal? (customattr-parent asm-row) (cons 'assembly 1))
  (check-equal? (car (customattr-ctor asm-row)) 'memberref "external attribute ctor is a MemberRef")
  (check-equal? (customattr-value asm-row) (bytes #x01 #x00 #x01 #x78 #x00 #x00))
  (define class-row (second rows))
  (check-equal? (customattr-parent class-row) (cons 'typedef (tdef-rid-of p "Widget")))
  (define method-row (third rows))
  (check-equal? (customattr-parent method-row) (cons 'methoddef (mdef-rid-of p "Run")))
  (check-equal? (customattr-ctor method-row) (cons 'methoddef (mdef-rid-of p ".ctor"))
                "a same-module constructor is a MethodDef")
  (check-equal? (customattr-value method-row) (bytes #x01 #x00 #x00 #x00)))

(test-case "build-metadata writes the CustomAttribute rows, sorted by Parent, and they read back"
  (define p (lower-module (parse-il (apply program marker-and-widget))))
  (define rdr
    (read-metadata-root (chunk-bytes (build-metadata p "custom-test" "custom-test.exe"))))
  (define rows (for/list ([i (in-range 1 4)]) (read-row rdr 'customattribute i)))
  ; HasCustomAttribute tags (II.24.2.6): methoddef 0, typedef 3, assembly 14. The table is sorted by
  ; the Parent coded value, so the assembly row (46) comes before MethodDef row 3 (96) and TypeDef 3 (99).
  (check-equal? (map (λ (r) (vector-ref r 0)) rows)
                (list (cons 'assembly 1) (cons 'methoddef (mdef-rid-of p "Run"))
                      (cons 'typedef (tdef-rid-of p "Widget"))))
  (check-equal? (vector-ref (first rows) 2) (bytes #x01 #x00 #x01 #x78 #x00 #x00))
  (check-equal? (vector-ref (second rows) 2) (bytes #x01 #x00 #x00 #x00)))

(define (parse-class-with custom-node)
  (parse-il (program `(.class (public auto ansi) Widget [,custom-node]))))

(test-case "a blob without the 0x0001 prolog is rejected (II.23.3)"
  (check-exn #rx"prolog 01 00"
             (λ () (parse-class-with
                    '(.custom (mscorlib System.ObsoleteAttribute) .ctor void (string)
                              = (bytearray (00 00 01 78 00 00)))))))

(test-case "a .custom constructor must return void"
  (check-exn #rx"returns void"
             (λ () (parse-class-with
                    '(.custom (mscorlib System.ObsoleteAttribute) .ctor int32 (string)
                              = (bytearray (01 00)))))))

(test-case "a same-module .custom qualifier must be Owner::.ctor"
  (check-exn #rx"malformed .custom"
             (λ () (parse-class-with '(.custom Marker.ctor void () = (bytearray (01 00)))))))

(test-case "a non-hex blob byte is rejected"
  (check-exn #rx"ZZ is not a hex byte"
             (λ () (parse-class-with
                    '(.custom (mscorlib System.ObsoleteAttribute) .ctor void (string)
                              = (bytearray (01 00 ZZ)))))))

(test-case "a .custom naming a constructor this module does not declare fails in lowering"
  (check-exn #rx"no constructor Nope"
             (λ () (lower-module (parse-il (program `(.class (public auto ansi) Widget
                                                       [(.custom Nope::.ctor void () = (bytearray (01 00)))])))))))
