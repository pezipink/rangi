(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly interfaces {})
  (.module interfaces.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class IArea) square) ((class IArea) triangle)))
       (newobj (Square) ())
       (stloc.0)
       (newobj (Triangle) ())
       (stloc.1)
       ; Square implements IArea.Area by returning 4; the callvirt through an IArea local dispatches to it: 4
       (ldloc.0)
       (callvirt int32 (IArea) Area ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Triangle implements IArea.Area by returning 6: 6
       (ldloc.1)
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
  (.class (public auto ansi) Triangle
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
       (ldc.i4.6)
       (ret)
       })
     (.implements IArea)
     ])
  )
