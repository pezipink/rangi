(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly win32-resources {})
  (.module win32-resources.exe)
  ; Win32 resource (PE/COFF, The .rsrc Section): type 16 (RT_VERSION), name 1, language 1033 (en-US);
  ; the four bytes 01..04 are its data, found through the resource directory in data directory 2
  (.win32resource 16 1 1033 (bytearray (01 02 03 04)))
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (ldstr "win32 resources")
       (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     ])
  )
