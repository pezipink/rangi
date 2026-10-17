(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-eh.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.try (catch (mscorlib System.Exception)) try_start try_end handler_start handler_end)
       (ldc.i4 7) (call void (mscorlib System.Console) WriteLine (int32))
       try_start:
       (ldc.i4 1) (ldc.i4.0) (div) (pop)
       (leave after)
       try_end:
       handler_start:
       (pop)
       (ldc.i4 99) (call void (mscorlib System.Console) WriteLine (int32))
       (leave after)
       handler_end:
       after:
       (ret)
       })
     ]))
