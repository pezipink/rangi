(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly il-unverifiable-opcodes {})
  (.module il-unverifiable-opcodes.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; nothing here calls the methods below: they are checked for layout and metadata only
       (ldstr "ok") (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     ])
  (.class (public auto ansi) Helpers
    [
     ; jmp transfers control to Target with the caller's arguments, which here are none
     (.method
       (public static) void Jumper () (cil managed)
       {
        (jmp void (Helpers) Target ())
       (ret)
       })
     (.method
      (public static) void Target () (cil managed)
      {
       (ldstr "jumped") (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     ; localloc allocates 16 bytes on the stack; the result is discarded
     (.method
      (public static) void Allocate () (cil managed)
      {
       (ldc.i4 16) (localloc) (pop)
       (ret)
       })
     ; cpblk copies 4 bytes between two null native-int addresses
     (.method
      (public static) void Copy () (cil managed)
      {
       (ldc.i4 0) (conv.i) (ldc.i4 0) (conv.i) (ldc.i4 4) (cpblk)
       (ret)
       })
     ; initblk fills 4 bytes at a null native-int address with zero
     (.method
      (public static) void Fill () (cil managed)
      {
       (ldc.i4 0) (conv.i) (ldc.i4 0) (ldc.i4 4) (initblk)
       (ret)
       })
     ; arglist pushes the argument handle of a vararg method
     (.method
      (public static) void Args () (cil managed)
      {
       (arglist) (pop)
       (ret)
       })
     ; ldvirtftn resolves the instance method Inst on the object at the top of the stack
     (.method
      (public static) void Virtual () (cil managed)
      {
       (ldnull) (ldvirtftn void (Helpers) Inst ()) (pop)
       (ret)
       })
     (.method
      (public) void Inst () (cil managed)
      {
       (ret)
       })
     ]))
