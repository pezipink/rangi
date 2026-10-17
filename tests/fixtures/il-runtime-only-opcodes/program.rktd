(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly il-runtime-only-opcodes {})
  (.module il-runtime-only-opcodes.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (call void (Helpers) Typed ())
       (call void (Helpers) Indirect ())
       (ret)
       })
     ])
  ; Neither verifier accepts this IL: ILVerify does not implement TypedReference or calli, and PEVerify
  ; rejects the calli. The fixture is checked by running it only.
  (.class (public auto ansi) Helpers
    [
     (.method
      (public static) void Typed () (cil managed)
      {
       (.locals init (int32))
       ; mkrefany makes a typed reference to local 0, and refanyval reads it back; prints 5
       (ldc.i4 5) (stloc.0)
       (ldloca.s 0) (mkrefany int32) (refanyval int32) (ldind.i4)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method
      (public static) void Indirect () (cil managed)
      {
       ; ldftn takes the address of Target, and calli calls it through that pointer; prints via calli
       (ldftn void (Helpers) Target ())
       (calli void ())
       (ret)
       })
     (.method
      (public static) void Target () (cil managed)
      {
       (ldstr "via calli") (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     ]))
