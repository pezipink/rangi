(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly managed-resources {})
  (.module managed-resources.exe)
  ; embedded managed resource (II.22.24): the five bytes 01..05 are stored in the CLI resources blob (II.25.3.3)
  (.mresource public Data (bytearray (01 02 03 04 05)))
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init (((class (mscorlib System.IO.Stream)) stream)))
       (call (class (mscorlib System.Reflection.Assembly)) (mscorlib System.Reflection.Assembly) GetExecutingAssembly ())
       (ldstr "Data")
       (callvirt (class (mscorlib System.IO.Stream)) (mscorlib System.Reflection.Assembly) GetManifestResourceStream (string))
       (stloc.0)
       ; the resource is five bytes long
       (ldloc.0)
       (callvirt int64 (mscorlib System.IO.Stream) get_Length ())
       (call void (mscorlib System.Console) WriteLine (int64))
       ; its first byte is 01
       (ldloc.0)
       (callvirt int32 (mscorlib System.IO.Stream) ReadByte ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  )
