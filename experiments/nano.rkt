#lang racket
(require "../src/ilasm/syntax.rkt" "../src/image.rkt")

(define nano
  '(
    (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
    (.assembly donothing {})
    (.module nano.exe)
    (.class (private auto ansi) <Module>           
      [
       (.method
        (public static) void main () (cil managed)
        {
         (.entrypoint)
         (.maxstack 8)
         (ldc.i 42)
         (call void (mscorlib System.Console) WriteLine (int32))
         (ret)     
        }) 
       ])))
(define nano2
  '(
    (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
    (.assembly donothing {})
    (.module nano2.exe)
    (.class (private auto ansi) <Module>           
            [
             (.method
              (public static) void main () (cil managed)
              {
               (.entrypoint)
               (.maxstack 8)
               (ldc.i 42)
               (ldc.i 42)
              (add)
               (call void (mscorlib System.Console) WriteLine (int32))
               (ret)     
               })
      
             ]

     
            )))

; assembles the program into the temp directory, then runs it and prints its output
(define (build-and-run name program)
  (define exe (build-path (find-system-path 'temp-dir) (format "rangi-~a.exe" name)))
  (assemble (parse-il program) exe)
  (void (system* exe)))

(build-and-run 'nano nano)
(build-and-run 'nano2 nano2)
