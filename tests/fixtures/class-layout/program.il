// Textual ilasm source for the class-layout differential check. It mirrors program.rktd.
// Overlay is explicit with fields at offsets 0 and 4. Packed is sequential with a marshaled field.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'class-layout' { }
.module 'class-layout.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    .locals init (valuetype Overlay V0, valuetype Packed V1)
    // the explicit struct: lo at offset 0 and hi at offset 4 read back as written: 7, 35
    ldloca.s V0
    ldc.i4 7
    stfld int32 Overlay::lo
    ldloca.s V0
    ldc.i4 35
    stfld int32 Overlay::hi
    ldloca.s V0
    ldfld int32 Overlay::lo
    call void [mscorlib]System.Console::WriteLine(int32)
    ldloca.s V0
    ldfld int32 Overlay::hi
    call void [mscorlib]System.Console::WriteLine(int32)
    // the sequential struct: a and its marshaled field b, read back: 40, 2
    ldloca.s V1
    ldc.i4 40
    stfld int32 Packed::a
    ldloca.s V1
    ldc.i4.2
    stfld int32 Packed::b
    ldloca.s V1
    ldfld int32 Packed::a
    call void [mscorlib]System.Console::WriteLine(int32)
    ldloca.s V1
    ldfld int32 Packed::b
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public explicit ansi sealed Overlay extends [mscorlib]System.ValueType
{
  .pack 4
  .size 8
  .field [0] public int32 lo
  .field [4] public int32 hi
}

.class public sequential ansi sealed Packed extends [mscorlib]System.ValueType
{
  .pack 2
  .size 12
  .field public int32 a
  .field public marshal(int32) int32 b
}
