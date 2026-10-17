(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly enum-literals {})
  (.module enum-literals.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((valuetype Color) c)))
       (ldc.i4.2)
       (call int32 (Program) Scale ((valuetype Color)))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.1)
       (stloc.0)
       (ldloc.0)
       (call int32 (Program) Scale ((valuetype Color)))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method (public static) int32 Scale ((valuetype Color)) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldc.i 10)
       (mul)
       (ret)
       })
     ])
  (.class (public sealed auto ansi) Color
    (.extends (mscorlib System.Enum))
    [
     (.field (public specialname rtspecialname) int32 value__)
     (.field (public static literal) (valuetype Color) Red = (int32 0))
     (.field (public static literal) (valuetype Color) Green = (int32 1))
     (.field (public static literal) (valuetype Color) Blue = (int32 2))
     ])
  )
