// Textual ilasm source for the value-types differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'value-types' { }
.module 'value-types.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    .locals init (valuetype Pair V_0, valuetype Pair V_1, valuetype Pair V_2)
    // p = Pair(20, 22), built in place through its address with the .ctor call
    ldloca.s 0
    ldc.i4 20
    ldc.i4 22
    call instance void Pair::.ctor(int32, int32)
    // Sum takes p by value and adds its fields: 42
    ldloc.0
    call int32 Ops::Sum(valuetype Pair)
    call void [mscorlib]System.Console::WriteLine(int32)
    // Swap takes p by value and returns a new Pair with the fields exchanged: q = (22, 20)
    ldloc.0
    call valuetype Pair Ops::Swap(valuetype Pair)
    stloc.1
    // q.first read through ldloca and ldfld: 22
    ldloca.s 1
    ldfld int32 Pair::first
    call void [mscorlib]System.Console::WriteLine(int32)
    // q.second read the same way: 20
    ldloca.s 1
    ldfld int32 Pair::second
    call void [mscorlib]System.Console::WriteLine(int32)
    // z = Pair(7, 8), then initobj zeroes it, so its first field reads 0
    ldloca.s 2
    ldc.i4.7
    ldc.i4.8
    call instance void Pair::.ctor(int32, int32)
    ldloca.s 2
    initobj Pair
    ldloca.s 2
    ldfld int32 Pair::first
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public auto ansi Ops
{
  // a value type parameter is passed by value, and its fields are read with ldfld
  .method public static int32 Sum(valuetype Pair p) cil managed
  {
    .maxstack 8
    ldarg.0
    ldfld int32 Pair::first
    ldarg.0
    ldfld int32 Pair::second
    add
    ret
  }

  // a value type is returned by value; the new Pair is built in a local and loaded
  .method public static valuetype Pair Swap(valuetype Pair p) cil managed
  {
    .maxstack 8
    .locals init (valuetype Pair V_0)
    ldloca.s 0
    ldarg.0
    ldfld int32 Pair::second
    ldarg.0
    ldfld int32 Pair::first
    call instance void Pair::.ctor(int32, int32)
    ldloc.0
    ret
  }
}

// Pair is declared after the class that uses it
.class public sequential ansi sealed Pair extends [mscorlib]System.ValueType
{
  .field public int32 first
  .field public int32 second

  .method public specialname rtspecialname instance void .ctor(int32, int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.1
    stfld int32 Pair::first
    ldarg.0
    ldarg.2
    stfld int32 Pair::second
    ret
  }
}
