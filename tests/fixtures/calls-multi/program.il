// Textual ilasm source for the calls-multi differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'calls-multi' { }
.module 'calls-multi.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    call int32 Program::seven()
    call void Program::show(int32)
    ldc.i4.5
    call int32 Program::fact(int32)
    call void Program::show(int32)
    ldc.i4.s 10
    call int32 Program::fib(int32)
    call void Program::show(int32)
    ldc.i4.3
    call int32 Program::quad(int32)
    call void Program::show(int32)
    ldc.i4.7
    call int32 Util::square(int32)
    call void Program::show(int32)
    ldc.i4.2
    ldc.i4.3
    call int32 Program::'add'(int32, int32)
    call void Program::show(int32)
    ret
  }

  .method public static void show(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }

  .method public static int32 seven() cil managed
  {
    .maxstack 8
    ldc.i4.7
    ret
  }

  .method public static int32 quad(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    call int32 Program::twice(int32)
    call int32 Program::twice(int32)
    ret
  }

  .method public static int32 twice(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.0
    call int32 Program::'add'(int32, int32)
    ret
  }

  .method public static int32 'add'(int32, int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.1
    add
    ret
  }

  .method public static int32 fib(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldc.i4.2
    blt base_case
    ldarg.0
    ldc.i4.1
    sub
    call int32 Program::fib(int32)
    ldarg.0
    ldc.i4.2
    sub
    call int32 Program::fib(int32)
    add
    ret
  base_case:
    ldarg.0
    ret
  }

  .method public static int32 fact(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldc.i4.2
    blt base_case
    ldarg.0
    ldarg.0
    ldc.i4.1
    sub
    call int32 Program::fact(int32)
    mul
    ret
  base_case:
    ldc.i4.1
    ret
  }
}

.class private auto ansi Util
{
  .method public static int32 square(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.0
    mul
    ret
  }
}
