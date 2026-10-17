#lang racket/base
; Palindrome checker built with Rangi as a library. library.dll holds the Palindrome class with
; a public static IsPalindrome(string). palindrome.exe links it and prints the result for a few
; words. Both images go into a temp directory, which is removed after the run.
; Expected stdout: True, True, False, True, one per line.
(require racket/file racket/system "../src/ilasm/syntax.rkt" "../src/image.rkt")

(define mscorlib
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define palindrome-library
  `((.assembly extern ,mscorlib {})
    (.assembly library {})
    (.module library.dll)
    (.format pe32 dll)
    (.class (public auto ansi) Palindrome
      [
       (.method
        (public static) boolean IsPalindrome (string) (cil managed)
        {
         (.maxstack 8)
         (.locals init (int32 int32))
         ; i = 0, j = length - 1
         (ldc.i4.0) (stloc.0)
         (ldarg.0) (callvirt int32 (mscorlib System.String) get_Length ()) (ldc.i4.1) sub (stloc.1)
         loop:
         (ldloc.0) (ldloc.1) (bge yes)
         (ldarg.0) (ldloc.0) (callvirt char (mscorlib System.String) get_Chars (int32))
         (ldarg.0) (ldloc.1) (callvirt char (mscorlib System.String) get_Chars (int32))
         (bne.un no)
         (ldloc.0) (ldc.i4.1) add (stloc.0)
         (ldloc.1) (ldc.i4.1) sub (stloc.1)
         (br loop)
         yes:
         (ldc.i4.1) (ret)
         no:
         (ldc.i4.0) (ret)
         })
       ])))

(define palindrome-host
  `((.assembly extern ,mscorlib {})
    (.assembly extern "library.dll" {})
    (.assembly palindrome {})
    (.module palindrome.exe)
    (.class (private auto ansi) <Module>
      [
       (.method
        (public static) void main () (cil managed)
        {
         (.entrypoint)
         (.maxstack 8)
         (ldstr "racecar") (call boolean (library Palindrome) IsPalindrome (string))
         (call void (mscorlib System.Console) WriteLine (boolean))
         (ldstr "level") (call boolean (library Palindrome) IsPalindrome (string))
         (call void (mscorlib System.Console) WriteLine (boolean))
         (ldstr "rangi") (call boolean (library Palindrome) IsPalindrome (string))
         (call void (mscorlib System.Console) WriteLine (boolean))
         (ldstr "noon") (call boolean (library Palindrome) IsPalindrome (string))
         (call void (mscorlib System.Console) WriteLine (boolean))
         (ret)
         })
       ])))

(define dir (make-temporary-file "rangi-palindrome-~a" 'directory))
(dynamic-wind
 void
 (λ ()
   (define exe (build-path dir "palindrome.exe"))
   (assemble (parse-il palindrome-library) (build-path dir "library.dll"))
   ; parse-il reads the extern library.dll relative to the current directory, so the host is
   ; parsed where library.dll sits
   (parameterize ([current-directory dir])
     (assemble (parse-il palindrome-host) exe)
     (void (system* exe))))
 (λ () (delete-directory/files dir #:must-exist? #f)))
