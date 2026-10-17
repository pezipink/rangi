(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module switch-dispatch.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.locals init (int32))
       ; i runs over -1, 0, 1, 2, 3. The switch table has three entries, so -1 (an unsigned
       ; index far past the end) and 3 take the fall-through path (III.3.66).
       (ldc.i4 -1) (stloc.0)
       loop:
       (ldloc.0)
       (switch case0 case1 case2)
       ; fall-through: index out of range, prints -1
       (ldc.i4 -1) (call void (mscorlib System.Console) WriteLine (int32)) (br next)
       case0:
       (ldc.i4 100) (call void (mscorlib System.Console) WriteLine (int32)) (br next)
       case1:
       (ldc.i4 101) (call void (mscorlib System.Console) WriteLine (int32)) (br next)
       case2:
       (ldc.i4 102) (call void (mscorlib System.Console) WriteLine (int32))
       next:
       (ldloc.0) (ldc.i4.1) add (stloc.0)
       (ldloc.0) (ldc.i4.4) (blt loop)
       ; a switch with no entries always falls through, prints 7
       (ldc.i4.0) (switch)
       (ldc.i4 7) (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
