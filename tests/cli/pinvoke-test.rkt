#lang racket/base
; P/Invoke methods (II.15.5): a bodiless pinvokeimpl method lowers to a MethodDef with
; PinvokeImpl set, an ImplMap row (II.22.22) and a ModuleRef row per DLL (II.22.31).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/reader.rkt"
         "../../src/cli/flags.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (module-with . methods)
  `((.assembly extern ,mscorlib-path {})
    (.assembly pinvoke {})
    (.module pinvoke.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed)
         { (.entrypoint) (.maxstack 8) (ret) })
       ,@methods])))

(define (lower . methods) (lower-module (parse-il (apply module-with methods))))

(define (module-methods p) (append-map tdef-methods (cli-program-typedefs p)))

(define (method-named p name)
  (findf (λ (m) (equal? (mdef-name m) name)) (module-methods p)))

(define abs-decl
  '(.method (public static pinvokeimpl) int32 Abs (int32) (pinvokeimpl "msvcrt.dll" cdecl)))

(test-case "a bodiless pinvokeimpl method lowers with PinvokeImpl set and no body"
  (define p (lower abs-decl))
  (define m (method-named p "Abs"))
  (check-false (mdef-body m))
  (check-equal? (bitwise-and (mdef-flags m) #x2000) #x2000)
  (check-equal? (pinvokeinfo-dll (mdef-pinvoke m)) "msvcrt.dll")
  (check-equal? (pinvokeinfo-import-name (mdef-pinvoke m)) "Abs")
  (check-equal? (pinvokeinfo-flags (mdef-pinvoke m)) (pinvoke-attributes-flags 'cdecl #f #f))
  (check-false (mdef-pinvoke (method-named p "main"))))

(test-case "the entry point, charset and SupportsLastError set the MappingFlags"
  (define p (lower '(.method (public static pinvokeimpl) int32 Len (string)
                      (pinvokeimpl "msvcrt.dll" stdcall unicode lasterr (as strlen)))))
  (define info (mdef-pinvoke (method-named p "Len")))
  (check-equal? (pinvokeinfo-import-name info) "strlen")
  (check-equal? (pinvokeinfo-flags info) (bitwise-ior #x0300 #x0004 #x0040)
                "stdcall 0x0300, unicode 0x0004, SupportsLastError 0x0040"))

(test-case "the default calling convention is winapi and the charset is not specified"
  (define p (lower '(.method (public static pinvokeimpl) int32 Get () (pinvokeimpl "k.dll"))))
  (check-equal? (pinvokeinfo-flags (mdef-pinvoke (method-named p "Get"))) #x0100))

(test-case "pinvoke-attributes-flags rejects unknown conventions and charsets"
  (check-exn exn:fail? (λ () (pinvoke-attributes-flags 'pascal #f #f)))
  (check-exn exn:fail? (λ () (pinvoke-attributes-flags 'winapi 'utf8 #f))))

(test-case "a DLL used by several methods gets one ModuleRef row, numbered in first-use order"
  (define p (lower abs-decl
                   '(.method (public static pinvokeimpl) int32 Strlen (string)
                      (pinvokeimpl "msvcrt.dll" cdecl))
                   '(.method (public static pinvokeimpl) int32 Pid ()
                      (pinvokeimpl "kernel32.dll" winapi))))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "pinvoke" "pinvoke.exe"))))
  (check-equal? (vector-ref (read-row rdr 'moduleref 1) 0) "msvcrt.dll")
  (check-equal? (vector-ref (read-row rdr 'moduleref 2) 0) "kernel32.dll")
  (check-exn exn:fail? (λ () (read-row rdr 'moduleref 3))))

(test-case "ImplMap rows point at their MethodDef, are sorted by MemberForwarded, and name their module"
  (define p (lower '(.method (public static pinvokeimpl) int32 Pid ()
                      (pinvokeimpl "kernel32.dll" winapi))
                   abs-decl))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "pinvoke" "pinvoke.exe"))))
  ; main is MethodDef 1, Pid 2, Abs 3. Columns: MappingFlags, MemberForwarded, ImportName,
  ; ImportScope (a ModuleRef rid). Rows come out in MemberForwarded order (II.22.22).
  (define rows (for/list ([i (in-range 1 3)]) (read-row rdr 'implmap i)))
  (check-equal? (map (λ (r) (vector-ref r 1)) rows) (list (cons 'methoddef 2) (cons 'methoddef 3)))
  (check-equal? (map (λ (r) (vector-ref r 2)) rows) '("Pid" "Abs"))
  (check-equal? (map (λ (r) (vector-ref r 3)) rows) '(1 2)
                "Pid (kernel32, declared first) gets ModuleRef 1, Abs (msvcrt) gets 2"))

(test-case "P/Invoke MethodDef rows are preservesig (II.23.1.11) and other methods are not"
  (define p (lower abs-decl))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "pinvoke" "pinvoke.exe"))))
  ; MethodDef columns: RVA, ImplFlags, Flags, Name, Signature, ParamList
  (check-equal? (vector-ref (read-row rdr 'methoddef 1) 1) 0 "main")
  (check-equal? (vector-ref (read-row rdr 'methoddef 2) 1) #x80 "Abs"))

(test-case "a bodiless pinvokeimpl method needs a DLL name string"
  (check-exn #rx"needs a DLL name"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M ()
                             (pinvokeimpl cdecl)))))
  (check-exn #rx"the DLL name is empty"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M ()
                             (pinvokeimpl ""))))))

(test-case "a pinvokeimpl method cannot have a body, even one with a pinvokeimpl declaration"
  (check-exn #rx"cannot have a body"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M () (cil managed)
                             { (.maxstack 8) (ldc.i4.0) (ret) })))))

(test-case "pinvokeimpl and a declaration must come together, and options are checked"
  (check-exn #rx"needs a \\(pinvokeimpl"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M (int32)))))
  (check-exn #rx"has a pinvokeimpl declaration but no pinvokeimpl keyword"
             (λ () (lower '(.method (public static) int32 M (int32)
                             (pinvokeimpl "msvcrt.dll" cdecl)))))
  (check-exn #rx"unsupported option"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M ()
                             (pinvokeimpl "msvcrt.dll" pascal)))))
  (check-exn #rx"more than one calling convention"
             (λ () (lower '(.method (public static pinvokeimpl) int32 M ()
                             (pinvokeimpl "msvcrt.dll" cdecl stdcall))))))

(test-case "a body-less method without pinvokeimpl must be abstract"
  (check-exn #rx"only abstract methods may omit it"
             (λ () (lower '(.method (public static) int32 M ()))))
  (check-exn #rx"has a pinvokeimpl declaration but no pinvokeimpl keyword"
             (λ () (lower '(.method (public static) int32 M () (pinvokeimpl "x.dll"))))))
