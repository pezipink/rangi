// Textual ilasm source for the enum-literals differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'enum-literals' { }
.module 'enum-literals.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    .locals init (valuetype Color V_0)
    ldc.i4.2
    call int32 Program::Scale(valuetype Color)
    call void [mscorlib]System.Console::WriteLine(int32)
    ldc.i4.1
    stloc.0
    ldloc.0
    call int32 Program::Scale(valuetype Color)
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }

  .method public static int32 Scale(valuetype Color c) cil managed
  {
    .maxstack 8
    ldarg.0
    ldc.i4 10
    mul
    ret
  }
}

.class public sealed auto ansi Color extends [mscorlib]System.Enum
{
  .field public specialname rtspecialname int32 value__
  .field public static literal valuetype Color Red = int32(0)
  .field public static literal valuetype Color Green = int32(1)
  .field public static literal valuetype Color Blue = int32(2)
}
