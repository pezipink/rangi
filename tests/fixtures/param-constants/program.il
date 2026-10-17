// Textual ilasm source for the param-constants differential check. It mirrors program.rktd.
// Parameter names and attributes go in the signature; defaults go in .param directives, because
// ilasm rejects a default inside the signature. The entry point sits on Program rather than
// <Module>, because the CLR rejects entry points declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'param-constants' { }
.module 'param-constants.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // Add(100, 1, 2): the first argument plus the two named ones: 103
    ldc.i4 100
    ldc.i4.1
    ldc.i4.2
    call int32 Calc::Add(int32, int32, int32)
    call void [mscorlib]System.Console::WriteLine(int32)
    // Add(0, 40, 2): 42
    ldc.i4.0
    ldc.i4 40
    ldc.i4.2
    call int32 Calc::Add(int32, int32, int32)
    call void [mscorlib]System.Console::WriteLine(int32)
    // Wide(9) returns its argument: 9
    ldc.i4 9
    call int32 Calc::Wide(int8)
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public auto ansi Calc
{
  .field public static literal int32 Limit = int32(42)

  .method public static int32 Add(int32, [in] int32 a, [opt] int32 b) cil managed
  {
    .param [3] = int32(5)
    .maxstack 8
    ldarg.1
    ldarg.2
    add
    ldarg.0
    add
    ret
  }

  .method public static int32 Wide([opt] int8 w) cil managed
  {
    .param [1] = int8(-3)
    .maxstack 8
    ldarg.0
    ret
  }
}
