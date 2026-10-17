(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly vararg-call {})
  (.module vararg-call.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; the call site passes two extra arguments after the sentinel (II.23.2.2); prints the first, 42
       (ldc.i4 42) (ldc.i4 7) (ldc.i4 8)
       (call int32 (Helpers) First (int32 ... int32 int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 5)
       (call int32 (Helpers) First (int32 ...))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  ; a VARARG method: the trailing ... makes its signature VARARG with no sentinel (II.23.2.2)
  (.class (public auto ansi) Helpers
    [
     (.method
      (public static) int32 First ((param () int32 a) ...) (cil managed)
      {
       (ldarg.0) (ret)
       })
     ]))
