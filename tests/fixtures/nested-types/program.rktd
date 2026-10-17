(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly nested-types {})
  (.module nested-types.exe)
  (.class (public auto ansi) Outer
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; new Inner(20) and read its field back: 20
       (ldc.i 20)
       (newobj (Outer/Inner) (int32))
       (callvirt int32 (Outer/Inner) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a second instance, its field set by stfld on a dup: 21
       (ldc.i 0)
       (newobj (Outer/Inner) (int32))
       (dup)
       (ldc.i 21)
       (stfld Outer/Inner weight int32)
       (callvirt int32 (Outer/Inner) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; the nested class's static method: Twice(4) is 8
       (ldc.i 4)
       (call int32 (Outer/Inner) Twice (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.class (nested public auto ansi) Inner
       [
        (.field (public) int32 weight)
        (.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
         {
          (.maxstack 8)
          (ldarg.0)
          (call void (mscorlib System.Object) .ctor ())
          (ldarg.0)
          (ldarg.1)
          (stfld Outer/Inner weight int32)
          (ret)
         })
        (.method (public static) int32 Twice (int32) (cil managed)
         {
          (.maxstack 8)
          (ldarg.0)
          (ldarg.0)
          (add)
          (ret)
         })
        (.method (public) int32 Get () (cil managed)
         {
          (.maxstack 8)
          (ldarg.0)
          (ldfld Outer/Inner weight int32)
          (ret)
         })
        ])
     ]))
