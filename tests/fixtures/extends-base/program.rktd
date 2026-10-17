(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly extends-base {})
  (.module extends-base.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; new Derived(21): Get is inherited from Base, so it is called with Base as the owner: 21
       (ldc.i 21)
       (newobj (Derived) (int32))
       (dup)
       (callvirt int32 (Base) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Twice is declared on Derived and reads Base's field through this: 42
       (callvirt int32 (Derived) Twice ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a second object, to show the inherited field is per instance: 5
       (ldc.i 5)
       (newobj (Derived) (int32))
       (callvirt int32 (Base) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  ; Derived is declared before its base, which checks that bases resolve regardless of order
  (.class (public auto ansi) Derived
    (.extends Base)
    [
     (.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.1)
       (call void (Base) .ctor (int32))
       (ret)
       })
     (.method (public) int32 Twice () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Base weight int32)
       (ldarg.0)
       (ldfld Base weight int32)
       (add)
       (ret)
       })
     ])
  (.class (public auto ansi) Base
    (.extends (mscorlib System.Object))
    [
     (.field (public) int32 weight)
     (.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ldarg.0)
       (ldarg.1)
       (stfld Base weight int32)
       (ret)
       })
     (.method (public) int32 Get () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Base weight int32)
       (ret)
       })
     ]))
