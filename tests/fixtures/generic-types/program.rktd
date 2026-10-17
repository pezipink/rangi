(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly generic-types {})
  (.module generic-types.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class Box (int32)) boxed) ((class Holder ((class Square))) holder)))
       ; Box<int32> stores 41 in its T field and Get returns it: 41
       (ldc.i4 41)
       (newobj (class (Box) (int32)) (!0))
       (stloc.0)
       (ldloc.0)
       (callvirt !0 (class (Box) (int32)) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Holder<Square> is constrained to a reference type with a default constructor that implements
       ; IArea; Get returns the Square, whose IArea.Area returns 4
       (newobj (Square) ())
       (newobj (class (Holder) ((class Square))) (!0))
       (stloc.1)
       (ldloc.1)
       (callvirt !0 (class (Holder) ((class Square))) Get ())
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
     (.method (public) !0 Get () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Box Value !0)
       (ret)
       })
     ])
  (.class (public auto ansi) Holder (.typarams (T class .ctor (class IArea)))
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
       (stfld Holder Value !0)
       (ret)
       })
     (.method (public) !0 Get () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldfld Holder Value !0)
       (ret)
       })
     ])
  )
