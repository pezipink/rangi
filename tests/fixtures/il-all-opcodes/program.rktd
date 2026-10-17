(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly il-all-opcodes {})
  (.module il-all-opcodes.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; each group is a static method, so a group's stack state never leaks into another
       (call void (Helpers) BoxOps ())
       (call void (Helpers) AddressOps ())
       (call void (Helpers) ConstrainedOps ())
       (call void (Helpers) FunctionPointers ())
       (ret)
       })
     ])
  (.class (public auto ansi) Helpers
    [
     (.field (public static) int32 counter)
     (.method
      (public static) void BoxOps () (cil managed)
      {
       ; box and unbox.any round-trip an int32; prints 42
       (ldc.i4 42) (box int32) (unbox.any int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; unbox gives a managed pointer, read with ldind.i4; prints 7
       (ldc.i4 7) (box int32) (unbox int32) (ldind.i4)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; castclass to String succeeds and prints cast
       (ldstr "cast") (castclass (mscorlib System.String))
       (call void (mscorlib System.Console) WriteLine (string))
       ; isinst to String yields the same reference and prints isinst
       (ldstr "isinst") (isinst (mscorlib System.String))
       (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     (.method
      (public static) void AddressOps () (cil managed)
      {
       (.locals init (int32 int32))
       ; sizeof int32 is 4
       (sizeof int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; stobj stores 5 through local 0's address, and ldobj reads it back; prints 5
       (ldloca.s 0) (ldc.i4 5) (stobj int32)
       (ldloca.s 0) (ldobj int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; cpobj copies local 0 into local 1; prints 5
       (ldloca.s 1) (ldloca.s 0) (cpobj int32)
       (ldloc.1)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; initobj zeroes local 1; prints 0
       (ldloca.s 1) (initobj int32)
       (ldloc.1)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; ldtoken pushes a RuntimeTypeHandle, which pop discards
       (ldtoken int32) (pop)
       ; ldflda on a Store reads the field through its address; prints 3
       (ldc.i4 3) (newobj (Store) (int32))
       (ldflda Store weight int32) (ldind.i4)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; ldsflda writes the static counter through its address; ldsfld reads it back; prints 9
       (ldsflda Helpers counter int32) (ldc.i4 9) (stind.i4)
       (ldsfld Helpers counter int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     (.method
      (public static) void ConstrainedOps () (cil managed)
      {
       (.locals init (int32))
       ; constrained. int32 makes callvirt ToString on the int32 at local 0; prints 5
       (ldc.i4 5) (stloc.0)
       (ldloca.s 0)
       (constrained. int32)
       (callvirt string (mscorlib System.Object) ToString ())
       (call void (mscorlib System.Console) WriteLine (string))
       (ret)
       })
     (.method
      (public static) void FunctionPointers () (cil managed)
      {
       ; ldftn pushes the address of Target, which pop discards
       (ldftn void (Helpers) Target ())
       (pop)
       (ret)
       })
     (.method
      (public static) void Target () (cil managed)
      {
       (ret)
       })
     ])
  (.class (public auto ansi) Store
    [
     (.field (public) int32 weight)
     (.method (public specialname rtspecialname) void .ctor (int32) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (call void (mscorlib System.Object) .ctor ())
       (ldarg.0)
       (ldarg.1)
       (stfld Store weight int32)
       (ret)
       })
     ]))
