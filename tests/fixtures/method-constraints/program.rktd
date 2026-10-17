(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly method-constraints {})
  (.module method-constraints.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; Measure<T> has the constraint T : IArea, so the interface call on its argument is valid: 4
       (newobj (Square) ())
       (call int32 (Program) Measure (!!0) (inst (class Square)))
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Scale<T> has the constraint T : class Wide, so its call on Wide's Area is valid: 9
       (newobj (Wide) ())
       (call int32 (Program) Scale (!!0) (inst (class Wide)))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method (public static) int32 Measure (.typarams (T (class IArea))) (!!0) (cil managed)
      {
       (.maxstack 8)
       (ldarga.s 0)
       (constrained. !!0)
       (callvirt int32 (IArea) Area ())
       (ret)
       })
     (.method (public static) int32 Scale (.typarams (T (class Wide))) (!!0) (cil managed)
      {
       (.maxstack 8)
       (ldarga.s 0)
       (constrained. !!0)
       (callvirt int32 (Wide) Area ())
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
     (.implements IArea)
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
     ])
  (.class (public auto ansi) Wide
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
       (ldc.i4 9)
       (ret)
       })
     ])
  )
