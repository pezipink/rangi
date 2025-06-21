#lang racket
(require "cli-writer.rkt") 

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
(time (assemble (parse-il nano)))