(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly typedref-param {})
  (.module typedref-param.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; a TypedReference is passed as an argument (II.23.2.1, II.23.1.16); prints 5
       (.locals init (int32))
       (ldc.i4 5) (stloc.0)
       (ldloca.s 0) (mkrefany int32)
       (call void (Helpers) Show (typedref))
       (ret)
       })
     ])
  (.class (public auto ansi) Helpers
    [
     (.method
      (public static) void Show ((param () typedref r)) (cil managed)
      {
       (ldarg.0) (refanyval int32) (ldind.i4)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
