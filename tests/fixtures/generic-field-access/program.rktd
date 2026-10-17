(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly generic-field-access {})
  (.module generic-field-access.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class Box (int32)) boxed) ((class Box ((class Square))) holder)))
       ; main is outside Box, so Value is reached through the MemberRef on Box<int32>.
       ; stfld stores 42, then ldfld reads it back: 42
       (ldc.i4 41)
       (newobj (class (Box) (int32)) (!0))
       (stloc.0)
       (ldloc.0)
       (ldc.i4 42)
       (stfld (class (Box) (int32)) Value int32)
       (ldloc.0)
       (ldfld (class (Box) (int32)) Value int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; ldflda gives the address of Value, which stind.i4 overwrites with 7: 7
       (ldloc.0)
       (ldflda (class (Box) (int32)) Value int32)
       (ldc.i4.7)
       (stind.i4)
       (ldloc.0)
       (ldfld (class (Box) (int32)) Value int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Box<Square> loads the Square through Value, whose IArea.Area returns 4
       (newobj (Square) ())
       (newobj (class (Box) ((class Square))) (!0))
       (stloc.1)
       (ldloc.1)
       (ldfld (class (Box) ((class Square))) Value (class Square))
       (callvirt int32 (IArea) Area ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public abstract interface auto ansi) IArea
    [
     (.method (public virtual abstract newslot) int32 Area ())
     ])
  (.class (public auto ansi) Square
    (.extends (mscorlib System.Object))
    [
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ret)
       })
     (.method (public virtual newslot) int32 Area () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4.4)
       (ret)
       })
     (.implements IArea)
     ])
  (.class (public auto ansi) Box (.typarams (T))
    (.extends (mscorlib System.Object))
    [
     (.field (public) !0 Value)
     (.method (public specialname rtspecialname) void .ctor (!0) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ldarg.0)
       (ldarg.1)
       (stfld Box Value !0)
       (ret)
       })
     ])
  )
