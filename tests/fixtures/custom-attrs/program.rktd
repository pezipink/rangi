(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly custom-attrs {})
  (.module custom-attrs.exe)
  ; assembly-level attribute: AssemblyTitleAttribute("rangi"), a literal blob (II.23.3)
  (.custom (mscorlib System.Reflection.AssemblyTitleAttribute) .ctor void (string) = (bytearray (01 00 05 72 61 6E 67 69 00 00)))
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; Widget.Get carries a same-module attribute (Tag) and returns 42
       (call int32 (Widget) Get ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  ; Tag is a same-module attribute class; its constructor is a MethodDef in this module
  (.class (public auto ansi) Tag
    (.extends (mscorlib System.Object))
    [
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ret)
       })
     ])
  ; Widget is marked by ObsoleteAttribute on the class (external MemberRef constructor)
  (.class (public auto ansi) Widget
    (.extends (mscorlib System.Object))
    [
     (.custom (mscorlib System.ObsoleteAttribute) .ctor void (string) = (bytearray (01 00 05 72 61 6E 67 69 00 00)))
     (.method (public specialname rtspecialname) void .ctor () (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ret)
       })
     (.method (public static) int32 Get () (cil managed)
      {
       (.custom Tag::.ctor void () = (bytearray (01 00 00 00)))
       (.maxstack 8)
       (ldc.i4 42)
       (ret)
       })
     ])
  )
