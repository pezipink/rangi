; Bounded multi-dimensional arrays end to end (II.14.2, II.23.2.13). main creates an int32[5..6, 3..5]
; (lower bounds 5 and 3, sizes 2 and 3) with newobj on the array type. The pair constructor takes
; (lowerbound, size) for each dimension, so the arguments are 5 2 3 3. Element [5+i,3+j] gets
; i*3+j+1 through Set, and the sum comes from Get over the same indices. Address returns a managed
; pointer to element [6,4], which stind.i4 overwrites with 42, and Get reads it back. Rank and the
; lower bounds come from System.Array on the same array. Expected stdout: 21, 42, 2, 5, 3, 3, one per line.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly bounded-arrays {})
  (.module bounded-arrays.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init ((array int32 2 (2 3) (5 3)) int32 int32 int32))
       (ldc.i4.5) (ldc.i4.2) (ldc.i4.3) (ldc.i4.3)
       (newobj (array int32 2 (2 3) (5 3)) (int32 int32 int32 int32)) (stloc.0)
       (ldc.i4.0) (stloc.1)
       fill-outer:
       (ldloc.1) (ldc.i4.2) (bge fill-done)
       (ldc.i4.0) (stloc.2)
       fill-inner:
       (ldloc.2) (ldc.i4.3) (bge fill-inner-done)
       (ldloc.0) (ldloc.1) (ldc.i4.5) add (ldloc.2) (ldc.i4.3) add
       (ldloc.1) (ldc.i4.3) mul (ldloc.2) add (ldc.i4.1) add
       (call instance void (array int32 2 (2 3) (5 3)) Set (int32 int32 int32))
       (ldloc.2) (ldc.i4.1) add (stloc.2)
       (br fill-inner)
       fill-inner-done:
       (ldloc.1) (ldc.i4.1) add (stloc.1)
       (br fill-outer)
       fill-done:
       (ldc.i4.0) (stloc.3)
       (ldc.i4.0) (stloc.1)
       sum-outer:
       (ldloc.1) (ldc.i4.2) (bge sum-done)
       (ldc.i4.0) (stloc.2)
       sum-inner:
       (ldloc.2) (ldc.i4.3) (bge sum-inner-done)
       (ldloc.3)
       (ldloc.0) (ldloc.1) (ldc.i4.5) add (ldloc.2) (ldc.i4.3) add
       (call instance int32 (array int32 2 (2 3) (5 3)) Get (int32 int32))
       add (stloc.3)
       (ldloc.2) (ldc.i4.1) add (stloc.2)
       (br sum-inner)
       sum-inner-done:
       (ldloc.1) (ldc.i4.1) add (stloc.1)
       (br sum-outer)
       sum-done:
       (ldloc.3) (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.6) (ldc.i4.4)
       (call instance (byref int32) (array int32 2 (2 3) (5 3)) Address (int32 int32))
       (ldc.i4.s 42) (stind.i4)
       (ldloc.0) (ldc.i4.6) (ldc.i4.4)
       (call instance int32 (array int32 2 (2 3) (5 3)) Get (int32 int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (call instance int32 (mscorlib System.Array) get_Rank ())
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.0) (call instance int32 (mscorlib System.Array) GetLowerBound (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.1) (call instance int32 (mscorlib System.Array) GetLowerBound (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloc.0) (ldc.i4.1) (call instance int32 (mscorlib System.Array) GetLength (int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ]))
