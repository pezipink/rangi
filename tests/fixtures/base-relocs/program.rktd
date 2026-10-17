(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly base-relocs {})
  (.module base-relocs.exe)
  ; a data block so the image has a .sdata section between .text and .reloc
  (.data D_Value = (bytearray (2A 00 00 00)))
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (ldsfld Table Value int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Table
    [
     (.field (public static) int32 Value at D_Value)
     ]))
