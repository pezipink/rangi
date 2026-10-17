; Managed DLL library, written with (.format pe32 dll): IMAGE_FILE_DLL is set and the image
; entry is the _CorDllMain stub, with no .entrypoint. The public static methods of Calc are
; called by the host EXE in program.rktd.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly library {})
  (.module library.dll)
  (.format pe32 dll)
  (.class (public auto ansi) Calc
    [
     (.method
      (public static) int32 answer () (cil managed)
      {
       (.maxstack 8)
       (ldc.i4 42)
       (ret)
       })
     (.method
      (public static) int32 add (int32 int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ldarg.1)
       add
       (ret)
       })
     ]))
