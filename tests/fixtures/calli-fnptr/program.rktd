(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly calli-fnptr {})
  (.module calli-fnptr.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; Apply receives a function pointer as an FNPTR-typed parameter and calls it with calli; prints 36
       (ldftn int32 (Helpers) Square (int32))
       (ldc.i4 6)
       (call int32 (Helpers) Apply ((fnptr int32 (int32)) int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Helpers
    [
     (.method
      (public static) int32 Apply ((param () (fnptr int32 (int32)) f) (param () int32 x)) (cil managed)
      {
       (ldarg.1) (ldarg.0) (calli int32 (int32)) (ret)
       })
     (.method
      (public static) int32 Square ((param () int32 x)) (cil managed)
      {
       (ldarg.0) (ldarg.0) (mul) (ret)
       })
     ]))
