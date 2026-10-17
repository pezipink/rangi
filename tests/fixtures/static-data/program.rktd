(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly static-data {})
  (.module static-data.exe)
  ; initial data blocks (II.16); each is named by the field that uses it
  (.data D_First = (bytearray (01 00 00 00)))
  (.data D_Second = (bytearray (10 00 00 00)))
  (.data D_Third = (bytearray (2A 00 00 00)))
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; data 01 00 00 00 reads as the little-endian int32 1
       (ldsfld Table First int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; a field with no data is zero-initialised
       (ldsfld Table Plain int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; the byte 10 is hex, so it is sixteen
       (ldsfld Table Second int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; the byte 2A is hex, so it is forty-two
       (ldsfld Table Third int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Table
    [
     (.field (public static) int32 First at D_First)
     (.field (public static) int32 Plain)
     (.field (public static) int32 Second at D_Second)
     (.field (public static) int32 Third at D_Third)
     ]))
