(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-branch.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.locals init (int32))
       ; loop: prints 0 1 2 3 4
       (ldc.i4.0) (stloc.0)
       loop:
       (ldloc.0) (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.1) add (stloc.0)
       (ldloc.0) (ldc.i4.5) (blt loop)
       ; beq: 3 == 3 taken, prints 1
       (ldc.i4 3) (ldc.i4 3) (beq t1)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n1)
       t1:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n1:
       ; bne.un: 3 != 4 taken, prints 1
       (ldc.i4 3) (ldc.i4 4) (bne.un t2)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n2)
       t2:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n2:
       ; blt: -1 < 1 signed, taken, prints 1
       (ldc.i4 -1) (ldc.i4 1) (blt t3)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n3)
       t3:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n3:
       ; bgt: 5 > 2 taken, prints 1
       (ldc.i4 5) (ldc.i4 2) (bgt t4)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n4)
       t4:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n4:
       ; ble: 2 <= 2 taken, prints 1
       (ldc.i4 2) (ldc.i4 2) (ble t5)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n5)
       t5:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n5:
       ; bge: 1 >= 2 not taken, prints 0
       (ldc.i4 1) (ldc.i4 2) (bge t6)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n6)
       t6:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n6:
       ; brtrue: 7 is true, taken, prints 1
       (ldc.i4 7) (brtrue t7)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n7)
       t7:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n7:
       ; brfalse: 0 is false, taken, prints 1
       (ldc.i4.0) (brfalse t8)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n8)
       t8:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n8:
       ; brtrue: 0 is false, not taken, prints 0
       (ldc.i4.0) (brtrue t9)
       (ldc.i4.0) (call void (mscorlib System.Console) WriteLine (int32)) (br n9)
       t9:
       (ldc.i4.1) (call void (mscorlib System.Console) WriteLine (int32))
       n9:
       ; long-form branch: the target is more than 127 bytes away, so beq must be promoted.
       ; The filler is stack-neutral; a taken branch skips the 99 line.
       (ldc.i4.1) (ldc.i4.1) (beq far)
       (ldc.i4 99) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop) (ldc.i4 1000000) (pop)
       far:
       (ldc.i4 42) (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
