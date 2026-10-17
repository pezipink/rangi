(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly instance-external-call {})
  (.module instance-external-call.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; instance keyword: non-virtual call to an external instance method, receiver first; prints 5
       (ldstr "hello") (call instance int32 (mscorlib System.String) get_Length ())
       (call void (mscorlib System.Console) WriteLine (int32))
       ; callvirt needs no keyword; prints 2
       (ldstr "hi") (callvirt instance int32 (mscorlib System.String) get_Length ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  )
