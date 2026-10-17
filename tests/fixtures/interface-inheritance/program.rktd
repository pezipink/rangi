(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly interface-inheritance {})
  (.module interface-inheritance.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class IB) square)))
       (newobj (Square) ())
       (stloc.0)
       ; IB extends IA, and Square.Area is routed to IA::Area through a MethodImpl: 4
       (ldloc.0)
       (callvirt int32 (IA) Area ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; IB declares Perimeter itself: 16
       (ldloc.0)
       (callvirt int32 (IB) Perimeter ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public abstract interface auto ansi) IA
    [
     (.method (public virtual abstract newslot) int32 Area ())
     ])
  (.class (public abstract interface auto ansi) IB
    [
     (.method (public virtual abstract newslot) int32 Perimeter ())
     (.implements IA)
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
     (.method (public virtual newslot) int32 Perimeter () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4 16)
       (ret)
       })
     (.override IA::Area int32 ())
     (.implements IB)
     ])
  )
