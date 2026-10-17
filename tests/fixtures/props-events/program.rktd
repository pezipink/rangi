(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly props-events {})
  (.module props-events.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class Box) box)))
       (newobj (Box) ())
       (stloc.0)
       ; set Value to 42 through its setter, then read it back through the getter: 42
       (ldloc.0)
       (ldc.i4 42)
       (callvirt void (Box) set_Value (int32))
       (ldloc.0)
       (callvirt int32 (Box) get_Value ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; the setter stores into the backing field, so a second write reads back as 7
       (ldloc.0)
       (ldc.i4 7)
       (callvirt void (Box) set_Value (int32))
       (ldloc.0)
       (callvirt int32 (Box) get_Value ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Box
    [
     (.field (private) int32 _value)
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ret)
       })
     (.method (public specialname) int32 get_Value () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Box _value int32)
       (ret)
       })
     (.method (public specialname) void set_Value (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.1)
       (stfld Box _value int32)
       (ret)
       })
     (.property instance int32 Value () (getter get_Value) (setter set_Value))
     (.method (public specialname) void add_Changed ((class (mscorlib System.EventHandler))) (cil managed)
      {
       (.maxstack 8)
       (ret)
       })
     (.method (public specialname) void remove_Changed ((class (mscorlib System.EventHandler))) (cil managed)
      {
       (.maxstack 8)
       (ret)
       })
     (.event (mscorlib System.EventHandler) Changed (add add_Changed) (remove remove_Changed))
     ])
  )
