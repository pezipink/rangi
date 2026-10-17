(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-conversions.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (ldc.i4 300) (conv.u1) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 200) (conv.i1) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.m1) (conv.u2) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 70000) (conv.i2) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i8 5000000000) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 -5) (conv.i8) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 7) (conv.r4) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.r8 -3.9) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.m1) (conv.u8) (conv.i4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.m1) (conv.u4) (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
