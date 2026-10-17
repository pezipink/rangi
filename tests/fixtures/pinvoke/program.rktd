(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly pinvoke {})
  (.module pinvoke.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; msvcrt abs(int), declared as Abs with entry point abs: 42
       (ldc.i4.s -42)
       (call int32 (Program) Abs (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       ; msvcrt strlen(char*), an ANSI string marshalled as LPStr: 5
       (ldstr "rangi")
       (call int32 (Program) StrLen (string))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method (public static pinvokeimpl) int32 Abs (int32) (pinvokeimpl "msvcrt.dll" cdecl (as abs)))
     (.method (public static pinvokeimpl) int32 StrLen (string) (pinvokeimpl "msvcrt.dll" cdecl (as strlen)))
     ])
  )
