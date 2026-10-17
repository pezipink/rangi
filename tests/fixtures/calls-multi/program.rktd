; Same-module calls (MethodDef tokens). main calls methods defined later in the class (forward
; calls), a chain quad -> twice -> add, two recursive methods, a zero-argument helper, and a
; call into the Util class. Expected stdout: 7 120 55 12 49 5, one per line.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module calls-multi.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (call int32 (Program) seven ()) (call void (Program) show (int32))
       (ldc.i4.5) (call int32 (Program) fact (int32)) (call void (Program) show (int32))
       (ldc.i4.s 10) (call int32 (Program) fib (int32)) (call void (Program) show (int32))
       (ldc.i4.3) (call int32 (Program) quad (int32)) (call void (Program) show (int32))
       (ldc.i4.7) (call int32 (Util) square (int32)) (call void (Program) show (int32))
       (ldc.i4.2) (ldc.i4.3) (call int32 (Program) add (int32 int32)) (call void (Program) show (int32))
       (ret)
       })
     (.method
      (public static) void show (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method
      (public static) int32 seven () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4.7)
       (ret)
       })
     (.method
      (public static) int32 quad (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call int32 (Program) twice (int32))
       (call int32 (Program) twice (int32))
       (ret)
       })
     (.method
      (public static) int32 twice (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.0)
       (call int32 (Program) add (int32 int32))
       (ret)
       })
     (.method
      (public static) int32 add (int32 int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.1)
       add
       (ret)
       })
     (.method
      (public static) int32 fib (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldc.i4.2)
       (blt base)
       (ldarg.0)
       (ldc.i4.1)
       sub
       (call int32 (Program) fib (int32))
       (ldarg.0)
       (ldc.i4.2)
       sub
       (call int32 (Program) fib (int32))
       add
       (ret)
       base:
       (ldarg.0)
       (ret)
       })
     (.method
      (public static) int32 fact (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldc.i4.2)
       (blt base)
       (ldarg.0)
       (ldarg.0)
       (ldc.i4.1)
       sub
       (call int32 (Program) fact (int32))
       mul
       (ret)
       base:
       (ldc.i4.1)
       (ret)
       })
     ])
  (.class (private auto ansi) Util
    [
     (.method
      (public static) int32 square (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.0)
       mul
       (ret)
       })
     ]))
