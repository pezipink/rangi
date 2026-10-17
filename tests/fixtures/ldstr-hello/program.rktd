(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ldstr-hello.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; A redirected console writes with the OEM code page, which cannot show the non-ASCII
       ; literal, so select UTF-8 first. Encoding.UTF8 is a static property getter.
       (call (class (mscorlib System.Text.Encoding)) (mscorlib System.Text.Encoding) get_UTF8 ())
       (call void (mscorlib System.Console) set_OutputEncoding ((class (mscorlib System.Text.Encoding))))
       ; ASCII literal: one UTF-16 code unit per character
       (ldstr "Hello, world")
       (call void (mscorlib System.Console) WriteLine (string))
       ; non-ASCII literal, written as escapes so the code points are unambiguous:
       ; U+00FC, U+00DF (BMP), U+4E16 U+754C (CJK), U+1F600 (a surrogate pair, two code units)
       (ldstr "Gr\u00FC\u00DFe, \u4E16\u754C \U0001F600")
       (dup)
       (call void (mscorlib System.Console) WriteLine (string))
       ; 11 code points but 12 UTF-16 code units, because U+1F600 is a surrogate pair
       (callvirt int32 (mscorlib System.String) get_Length ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
