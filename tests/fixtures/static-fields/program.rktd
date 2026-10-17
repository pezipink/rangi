(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly static-fields {})
  (.module static-fields.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; static int32 field: store, then read back and add one
       (ldc.i 41)
       (stsfld Store count int32)
       (ldsfld Store count int32)
       (ldc.i 1)
       (add)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; static string field: store a literal, then write it
       (ldstr "hello")
       (stsfld Store label string)
       (ldsfld Store label string)
       (call void (mscorlib System.Console) WriteLine (string))
       ; a static field of an external type, String.Empty, which is an empty line
       (ldsfld (mscorlib System.String) Empty string)
       (call void (mscorlib System.Console) WriteLine (string))
       ; a static field of this module's own class type, which starts null
       (ldnull)
       (stsfld Store next (class Store))
       (ldsfld Store next (class Store))
       (ldnull)
       (ceq)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Store
    [
     (.field (public static) int32 count)
     (.field (public static) string label)
     (.field (public static) (class Store) next)
     (.field (public) int32 weight)
     ]))
