; Host EXE for the dll-output fixture. library.dll is built beside this image by the fixture
; harness, and the .assembly extern "library.dll" resolves from that directory. Expected
; stdout: 42 then 5, one per line.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly extern "library.dll" {})
  (.assembly dll-output {})
  (.module dll-output.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (call int32 (library Calc) answer ()) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.2) (ldc.i4.3) (call int32 (library Calc) add (int32 int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
