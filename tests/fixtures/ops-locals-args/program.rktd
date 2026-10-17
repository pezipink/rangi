(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-locals-args.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.locals init (int32 int32 int32 int32))
       ; stloc.0 and ldloc.0 round-trip through the first local; prints 7
       (ldc.i4.7) (stloc.0)
       (ldloc.0) (call void (mscorlib System.Console) WriteLine (int32))
       ; stloc.1 and ldloc.1 use the short 1-byte form; prints 42
       (ldc.i4 42) (stloc.1)
       (ldloc.1) (call void (mscorlib System.Console) WriteLine (int32))
       ; ldloca.s and stind.i4 write local 2 through its address; prints 9
       (ldloca.s 2) (ldc.i4 9) (stind.i4)
       (ldloc.2) (call void (mscorlib System.Console) WriteLine (int32))
       ; ldloca.s with stind.i4 on local 3; ldloc.3 + ldc.i4.5 + add prints 45
       (ldloca.s 3) (ldc.i4 40) (stind.i4)
       (ldloc.3) (ldc.i4.5) add (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
