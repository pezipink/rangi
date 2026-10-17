(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module generic-calls.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) !!0 Id (.typarams T) (!!0) (cil managed)
      {
       (ldarg.0)
       (ret)
       })
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.locals init (((class (mscorlib System.Collections.Generic.List) (int32)) list)))
       (newobj (class (mscorlib System.Collections.Generic.List) (int32)) ())
       (stloc.0)
       (ldloc.0) (ldc.i4 41) (callvirt void (class (mscorlib System.Collections.Generic.List) (int32)) Add (!0))
       (ldloc.0) (ldc.i4.1) (callvirt void (class (mscorlib System.Collections.Generic.List) (int32)) Add (!0))
       (ldloc.0) (callvirt int32 (class (mscorlib System.Collections.Generic.List) (int32)) get_Count ())
       (ldc.i4.2) (bne.un fail)
       (ldc.i4.7) (call !!0 (Program) Id (!!0) (inst int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.0) (callvirt !0 (class (mscorlib System.Collections.Generic.List) (int32)) get_Item (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       fail:
       (ldc.i4.m1) (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
