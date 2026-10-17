(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly cmod-params {})
  (.module cmod-params.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; the modreq on the parameter and the modopt on the return type are part of the signature
       ; (II.23.2.7); the call matches the method only if it repeats them. Prints 42.
       (ldc.i4 41)
       (call (modopt (mscorlib System.Runtime.CompilerServices.IsConst) int32) (Helpers) Bump
             ((modreq (mscorlib System.Runtime.CompilerServices.IsVolatile) int32)))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Helpers
    [
     (.method
      (public static) (modopt (mscorlib System.Runtime.CompilerServices.IsConst) int32) Bump
      ((param () (modreq (mscorlib System.Runtime.CompilerServices.IsVolatile) int32) x))
      (cil managed)
      {
       (ldarg.0) (ldc.i4.1) (add) (ret)
       })
     ]))
