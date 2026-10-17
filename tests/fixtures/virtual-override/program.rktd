(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly virtual-override {})
  (.module virtual-override.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class Base) derived) ((class Base) plain)))
       (newobj (Derived) ())
       (stloc.0)
       (newobj (Base) ())
       (stloc.1)
       ; Get is overridden in Derived: the callvirt through a Base-typed local dispatches to it: 2
       (ldloc.0)
       (callvirt int32 (Base) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Describe is virtual and not overridden in Derived, so Base's body runs: 10
       (ldloc.0)
       (callvirt int32 (Base) Describe ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a Base object: its own Get runs: 1
       (ldloc.1)
       (callvirt int32 (Base) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Base
    (.extends (mscorlib System.Object))
    [
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ret)
       })
     (.method (public virtual newslot) int32 Get () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4.1)
       (ret)
       })
     (.method (public virtual newslot) int32 Describe () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4.s 10)
       (ret)
       })
     ])
  (.class (public auto ansi) Derived
    (.extends Base)
    [
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (Base) .ctor ())
       (ret)
       })
     (.method (public virtual) int32 Get () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4.2)
       (ret)
       })
     (.override Base::Get int32 ())
     ])
  )
