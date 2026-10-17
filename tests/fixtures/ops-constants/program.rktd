(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-constants.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (ldc.i4.m1) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.2) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.3) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.5) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.6) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.7) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.8) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.s -100) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 100000) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 -2147483648) (call void (mscorlib System.Console) WriteLine (int32))
       ; int64 constant, truncated to int32 by conv.i4: 5000000000 mod 2^32
       (ldc.i8 5000000000) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       ; float constants truncated toward zero by conv.i4
       (ldc.r8 3.7) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.r4 -2.5) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
