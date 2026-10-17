#lang racket/base
; Parameter rows and layout rows (II.22.33, II.22.9, II.22.8, II.22.16). Named parameters get Param
; rows with their flags and Sequence numbers. Default values and literal fields get Constant rows
; (blob II.23.1.15). ClassLayout records .pack and .size, and explicit field offsets become
; FieldLayout rows. A marshaled field gets a FieldMarshal row (II.23.2.6). These tests check the
; lowered values and the rows build-metadata writes, read back through read-row.
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
    (.assembly layout-test {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define (tdef-named p name)
  (findf (λ (td) (equal? (tdef-name td) name)) (cli-program-typedefs p)))

(define (method-named p class-name name)
  (findf (λ (md) (equal? (mdef-name md) name)) (tdef-methods (tdef-named p class-name))))

(define (field-named p class-name name)
  (findf (λ (fd) (equal? (fdef-name fd) name)) (tdef-fields (tdef-named p class-name))))

(define calc
  '(.class (public auto ansi) Calc
     [(.field (public static literal) int32 Limit = (int32 42))
      (.method (public static) int32 Add (int32 (param (in) int32 a) (param (opt) int32 b = (int32 5)))
        (cil managed) { (.maxstack 8) (ldc.i4.0) (ret) })
      (.method (public static) int32 Wide ((param (opt) int8 w = (int8 -3))) (cil managed)
        { (.maxstack 8) (ldc.i4.0) (ret) })
      (.method (public static) int32 Plain (int32 int32) (cil managed)
        { (.maxstack 8) (ldc.i4.0) (ret) })]))

(define layouts
  '((.class (public explicit ansi sealed) Overlay
      (.extends (mscorlib System.ValueType))
      [(.pack 4)
       (.size 8)
       (.field (public) int32 lo offset 0)
       (.field (public) int32 hi offset 4)])
    (.class (public sequential ansi sealed) Packed
      (.extends (mscorlib System.ValueType))
      [(.pack 2)
       (.size 12)
       (.field (public) int32 a)
       (.field (public) (marshal int32) int32 b)])
    (.class (public auto ansi) Plain2 [(.field (public) int32 x)])))

(test-case "named parameters get Param flags and Sequence numbers, and unnamed ones get no row (II.22.33)"
  (define p (lower calc))
  (define params (mdef-params (method-named p "Calc" "Add")))
  (check-equal? (map paramdef-name params) '("a" "b"))
  (check-equal? (map paramdef-sequence params) '(2 3) "position 1 is unnamed, so Sequence starts at 2")
  (check-equal? (map paramdef-flags params) (list 1 #x1010) "in is 0x1, optional with default is 0x1010")
  (check-equal? (mdef-params (method-named p "Calc" "Plain")) '() "a method with no names has no Param rows"))

(test-case "default values are Constant blobs in the parameter's element type (II.23.1.15)"
  (define p (lower calc))
  (define b (second (mdef-params (method-named p "Calc" "Add"))))
  (check-equal? (paramdef-const b) (cons 8 (bytes 5 0 0 0)) "int32 5 is I4 with four little-endian bytes")
  (define w (first (mdef-params (method-named p "Calc" "Wide"))))
  (check-equal? (paramdef-const w) (cons 4 (bytes #xFD)) "int8 -3 is I1 with one two's-complement byte"))

(test-case "a literal field has fdHasDefault and a Constant value (II.23.1.5, II.22.9)"
  (define limit (field-named (lower calc) "Calc" "Limit"))
  (check-not-false (bitwise-bit-set? (fdef-flags limit) 15) "fdHasDefault is 0x8000")
  (check-equal? (fdef-const limit) (cons 8 (bytes 42 0 0 0))))

(test-case "a default that does not match its parameter type is rejected"
  (check-exn exn:fail?
             (λ () (lower '(.class (public) Bad
                             [(.method (public static) int32 F ((param (opt) int32 x = (int8 1)))
                                (cil managed) { (ret) })])))))

(test-case "a default out of range for its parameter type is rejected"
  (check-exn exn:fail?
             (λ () (lower '(.class (public) Bad
                             [(.method (public static) int32 F ((param (opt) int8 x = (int8 300)))
                                (cil managed) { (ret) })])))))

(test-case "ClassLayout records .pack and .size, and a class without them has no ClassLayout (II.22.8)"
  (define p (apply lower layouts))
  (define overlay (tdef-layout (tdef-named p "Overlay")))
  (check-equal? (classlayout-pack overlay) 4)
  (check-equal? (classlayout-size overlay) 8)
  (define packed (tdef-layout (tdef-named p "Packed")))
  (check-equal? (classlayout-pack packed) 2)
  (check-equal? (classlayout-size packed) 12)
  (check-false (tdef-layout (tdef-named p "Plain2"))))

(test-case "explicit field offsets are kept, and fields without an offset have none (II.22.16)"
  (define p (apply lower layouts))
  (check-equal? (fdef-offset (field-named p "Overlay" "lo")) 0)
  (check-equal? (fdef-offset (field-named p "Overlay" "hi")) 4)
  (check-false (fdef-offset (field-named p "Packed" "a"))))

(test-case "a marshaled field has fdHasFieldMarshal and its native type (II.22.9, II.23.2.6)"
  (define p (apply lower layouts))
  (define b (field-named p "Packed" "b"))
  (check-equal? (fdef-marshal b) 7 "int32 is NATIVE_TYPE 0x07 (II.23.4)")
  (check-not-false (bitwise-bit-set? (fdef-flags b) 12) "fdHasFieldMarshal is 0x1000")
  (check-false (fdef-marshal (field-named p "Packed" "a"))))

(test-case "a class with .pack or .size but no explicit or sequential layout is rejected"
  (check-exn exn:fail?
             (λ () (lower '(.class (public auto ansi) X [(.pack 4)])))))

(test-case ".pack must be a power of two no larger than 128"
  (check-exn exn:fail?
             (λ () (lower '(.class (public sequential ansi) X [(.pack 3)])))))

(test-case "an explicit field offset needs an explicit layout"
  (check-exn exn:fail?
             (λ () (lower '(.class (public auto ansi) X [(.field (public) int32 x offset 0)])))))

(test-case "Param, Constant, ClassLayout, FieldLayout, and FieldMarshal rows read back as written"
  (define p (apply lower calc layouts))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "layout-test" "layout.dll"))))
  (check-equal? (vector-ref (read-row rdr 'param 1) 2) "a")
  (check-equal? (vector-ref (read-row rdr 'param 1) 1) 2)
  (check-equal? (vector-ref (read-row rdr 'param 2) 2) "b")
  (check-equal? (vector-ref (read-row rdr 'param 2) 0) #x1010)
  (check-equal? (vector-ref (read-row rdr 'param 3) 2) "w" "Wide's w is the third Param row")
  (check-exn exn:fail? (λ () (read-row rdr 'param 4)) "three named parameters, three rows")
  (check-equal? (vector-ref (read-row rdr 'constant 1) 0) 8 "Limit is I4")
  (check-equal? (vector-ref (read-row rdr 'classlayout 1) 0) 4)
  (check-equal? (vector-ref (read-row rdr 'classlayout 1) 1) 8)
  (check-equal? (vector-ref (read-row rdr 'classlayout 2) 0) 2)
  (check-equal? (vector-ref (read-row rdr 'classlayout 2) 1) 12)
  (check-equal? (vector-ref (read-row rdr 'fieldlayout 1) 0) 0)
  (check-equal? (vector-ref (read-row rdr 'fieldlayout 2) 0) 4)
  (check-equal? (vector-ref (read-row rdr 'fieldmarshal 1) 1) (bytes 7) "blob is the single NATIVE_TYPE byte (II.23.2.6)"))
