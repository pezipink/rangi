(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly cctor-init {})
  (.module cctor-init.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; the type initializer runs before the first static access, so both reads give 42
       (call int32 (Store) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldsfld Store value int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Store
    [
     (.field (public static) int32 value)
     ; the type initializer (II.10.5.3.1): static, specialname, rtspecialname, no parameters
     (.method (private static specialname rtspecialname) void .cctor () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4 6)
       (ldc.i4 7)
       (mul)
       (stsfld Store value int32)
       (ret)
       })
     (.method (public static) int32 Get () (cil managed)
      {
       (.maxstack 8)
       (ldsfld Store value int32)
       (ret)
       })
     ]))
