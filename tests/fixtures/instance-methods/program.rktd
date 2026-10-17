(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly instance-methods {})
  (.module instance-methods.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; new Store(41); Bump(1) on the same object (dup keeps a copy); Get gives 42
       (ldc.i 41)
       (newobj (Store) (int32))
       (dup)
       (ldc.i 1)
       (callvirt void (Store) Bump (int32))
       (callvirt int32 (Store) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a second object, to show each instance has its own weight: 7
       (ldc.i 7)
       (newobj (Store) (int32))
       (callvirt int32 (Store) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a non-virtual call to an instance method: Store(1), Bump(4) by call, Get gives 5
       (ldc.i 1)
       (newobj (Store) (int32))
       (dup)
       (ldc.i 4)
       (call void (Store) Bump (int32))
       (callvirt int32 (Store) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Store
    [
     (.field (public) int32 weight)
     (.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ldarg.0)
       (ldarg.1)
       (stfld Store weight int32)
       (ret)
       })
     (.method (public) int32 Get () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Store weight int32)
       (ret)
       })
     (.method (public) void Bump (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.0)
       (ldfld Store weight int32)
       (ldarg.1)
       (add)
       (stfld Store weight int32)
       (ret)
       })
     ]))
