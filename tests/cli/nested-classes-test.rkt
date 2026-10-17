#lang racket/base
; Nested types (II.10.3): a nested .class is written inside its enclosing class body. Each one gets
; a TypeDef whose flags carry the nested visibility, a simple name, and an empty namespace (II.22.37),
; and one NestedClass row (II.22.32). These tests check the parse, the TypeDef flags and names, the
; NestedClass rows as build-metadata writes them, and the errors for bad nesting.
(require rackunit
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/reader.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly nested-test {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

; Outer > A (nested public) > B (nested assembly); Outer > C (no keyword, so nested private)
(define nested-classes
  '(.class (public auto ansi) Outer
     [(.class (nested public auto ansi) A
        [(.class (nested assembly auto ansi) B [])])
      (.class (auto ansi) C [])]))

; the TypeDef named name in the lowered program, or #f
(define (tdef-named p name)
  (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs p)))

; the 1-based TypeDef rid of a named class: rids follow the order of cli-program-typedefs
(define (rid-of p name)
  (for/first ([td (in-list (cli-program-typedefs p))] [i (in-naturals 1)]
              #:when (equal? (tdef-name td) name))
    i))

(test-case "nested classes follow their enclosing class in depth-first source order"
  (define m (parse-il (program nested-classes)))
  (check-equal? (map class-decl-name (module-model-classes m))
                '(<Module> Program Outer Outer/A Outer/A/B Outer/C))
  (define b (findf (λ (c) (eq? (class-decl-name c) 'Outer/A/B)) (module-model-classes m)))
  (check-equal? (class-decl-enclosing b) 'Outer/A)
  (define outer (findf (λ (c) (eq? (class-decl-name c) 'Outer)) (module-model-classes m)))
  (check-false (class-decl-enclosing outer)))

(test-case "a nested TypeDef has the nested visibility flags (II.22.37)"
  (define p (lower nested-classes))
  (check-equal? (tdef-flags (tdef-named p "A")) 2 "nested public is NestedPublic 0x2")
  (check-equal? (tdef-flags (tdef-named p "B")) 5 "nested assembly is NestedAssembly 0x5")
  (check-equal? (tdef-flags (tdef-named p "C")) 3 "no keyword is nested private 0x3"))

(test-case "every nested visibility keyword maps to its TypeAttributes value (II.22.37)"
  (for ([kw (in-list '((nested public) (nested private) (nested family) (nested assembly)
                       (nested famandassem) (nested famorassem)))]
        [expected (in-list '(2 3 4 5 6 7))])
    (define p (lower `(.class (public) Outer [(.class (,@kw) N [])])))
    (check-equal? (tdef-flags (tdef-named p "N")) expected (format "~a" kw))))

(test-case "a nested TypeDef has its simple name and an empty namespace (II.22.37)"
  (define p (lower nested-classes))
  (check-equal? (tdef-name (tdef-named p "B")) "B")
  (check-equal? (tdef-ns (tdef-named p "B")) "")
  (check-equal? (tdef-enclosing (tdef-named p "B")) (rid-of p "A")))

(test-case "NestedClass rows pair each nested TypeDef with its enclosing TypeDef, sorted by nested rid (II.22.32)"
  (define p (lower nested-classes))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "nested-test" "nested.dll"))))
  (define a (rid-of p "A"))
  (define b (rid-of p "B"))
  (define c (rid-of p "C"))
  (define outer (rid-of p "Outer"))
  (check-equal? (vector-ref (read-row rdr 'nestedclass 1) 0) a)
  (check-equal? (vector-ref (read-row rdr 'nestedclass 1) 1) outer)
  (check-equal? (vector-ref (read-row rdr 'nestedclass 2) 0) b)
  (check-equal? (vector-ref (read-row rdr 'nestedclass 2) 1) a)
  (check-equal? (vector-ref (read-row rdr 'nestedclass 3) 0) c)
  (check-equal? (vector-ref (read-row rdr 'nestedclass 3) 1) outer)
  (check-exn exn:fail? (λ () (read-row rdr 'nestedclass 4)) "exactly one row per nested type"))

(test-case "a nested TypeDef row reads back with nested flags, its simple name, and an empty namespace"
  (define p (lower nested-classes))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "nested-test" "nested.dll"))))
  (define row (read-row rdr 'typedef (rid-of p "B")))
  (check-equal? (vector-ref row 0) 5)
  (check-equal? (vector-ref row 1) "B")
  (check-equal? (vector-ref row 2) ""))

(test-case "a top-level class has no NestedClass rows"
  (define p (lower '(.class (public) Plain [])))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "nested-test" "nested.dll"))))
  (check-exn exn:fail? (λ () (read-row rdr 'nestedclass 1))))

(test-case "a nested class with a missing enclosing class is rejected"
  (define m (parse-il (program '(.class (public) Keep []))))
  (define bad (module-model (module-model-asm-refs m)
                            (append (module-model-classes m)
                                    (list (class-decl '(nested public) 'Inner '() #f '() '() 'Missing '())))
                            (module-model-module-name m)
                            (module-model-format m)
                            (module-model-dll? m)
                            (module-model-subsystem m)
                           (module-model-platform m)
                           (module-model-data m)))
  (check-exn #rx"nested class Inner has no enclosing class Missing"
             (λ () (lower-module bad))))

(test-case "a nested class with no access keyword after nested is rejected"
  (check-exn #rx"nested class needs an access keyword after nested"
             (λ () (lower '(.class (public) Outer [(.class (nested) N [])])))))

(test-case "a bare access keyword in a nested class is rejected"
  (check-exn #rx"bare access keyword in nested class"
             (λ () (lower '(.class (public) Outer [(.class (public) N [])])))))

(test-case "nested visibility on a top-level class is rejected"
  (check-exn #rx"nested visibility on a top-level class"
             (λ () (lower '(.class (nested public) Top [])))))

(test-case "a top-level class name may not contain /"
  (check-exn #rx"class name Outer/X may not contain /"
             (λ () (parse-il (program '(.class (public) Outer/X []))))))

(test-case "a nested class name may not contain . or /"
  (check-exn #rx"nested class name a\\.b may not contain \\. or /"
             (λ () (parse-il (program '(.class (public) Outer [(.class (nested public) a.b [])]))))))

(test-case "<Module> cannot have nested classes"
  (check-exn #rx"<Module> cannot have nested classes"
             (λ () (parse-il `((.assembly extern ,mscorlib-path {})
                               (.assembly nested-test {})
                               (.module local.exe)
                               (.class (private auto ansi) <Module>
                                 [(.class (nested public) N [])
                                  (.method (public static) void main () (cil managed)
                                    { (.entrypoint) (.maxstack 8) (ret) })]))))))
