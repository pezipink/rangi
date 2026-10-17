; Arrays end to end. main allocates an int32[10] with newarr, fills it with squares 0..9 in a loop
; (stelem int32 with a local counter), passes it to sum (an int32[] parameter, II.23.2.12), and
; prints the total, one element through ldelem int32, and the length through ldlen. sum walks the
; array with ldlen, ldelem.i4, and a loop. Expected stdout: 285 9 10, one per line.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly arrays-sum {})
  (.module arrays-sum.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init ((szarray int32) int32))
       (ldc.i4.s 10) (newarr int32) (stloc.0)
       (ldc.i4.0) (stloc.1)
       fill:
       (ldloc.1) (ldc.i4.s 10) (bge filled)
       (ldloc.0) (ldloc.1) (ldloc.1) (ldloc.1) mul (stelem int32)
       (ldloc.1) (ldc.i4.1) add (stloc.1)
       (br fill)
       filled:
       (ldloc.0) (call int32 (Program) sum ((szarray int32))) (call void (Program) show (int32))
       (ldloc.0) (ldc.i4.3) (ldelem int32) (call void (Program) show (int32))
       (ldloc.0) ldlen (conv.i4) (call void (Program) show (int32))
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
      (public static) int32 sum ((szarray int32)) (cil managed)
      {
       (.maxstack 8)
       (.locals init (int32 int32))
       (ldc.i4.0) (stloc.0)
       (ldc.i4.0) (stloc.1)
       loop:
       (ldloc.1) (ldarg.0) ldlen (conv.i4) (bge done)
       (ldloc.0) (ldarg.0) (ldloc.1) ldelem.i4 add (stloc.0)
       (ldloc.1) (ldc.i4.1) add (stloc.1)
       (br loop)
       done:
       (ldloc.0) (ret)
       })
     ]))
