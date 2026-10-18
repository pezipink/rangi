// Textual ilasm source for the extends-base differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'extends-base' { }
.module 'extends-base.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // new Derived(21): Get is inherited from Base, so it is called with Base as the owner: 21
    ldc.i4 21
    newobj instance void Derived::.ctor(int32)
    dup
    callvirt instance int32 Base::Get()
    call void [mscorlib]System.Console::WriteLine(int32)
    // Twice is declared on Derived and reads Base's field through this: 42
    callvirt instance int32 Derived::Twice()
    call void [mscorlib]System.Console::WriteLine(int32)
    // a second object, to show the inherited field is per instance: 5
    ldc.i4 5
    newobj instance void Derived::.ctor(int32)
    callvirt instance int32 Base::Get()
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

// Derived is declared before its base, which checks that bases resolve regardless of order
.class public auto ansi Derived extends Base
{
  .method public specialname rtspecialname instance void .ctor(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.1
    call instance void Base::.ctor(int32)
    ret
  }

  .method public instance int32 Twice() cil managed
  {
    .maxstack 8
    ldarg.0
    ldfld int32 Base::weight
    ldarg.0
    ldfld int32 Base::weight
    add
    ret
  }
}

.class public auto ansi Base extends [mscorlib]System.Object
{
  .field public int32 weight

  .method public specialname rtspecialname instance void .ctor(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    call instance void [mscorlib]System.Object::.ctor()
    ldarg.0
    ldarg.1
    stfld int32 Base::weight
    ret
  }

  .method public instance int32 Get() cil managed
  {
    .maxstack 8
    ldarg.0
    ldfld int32 Base::weight
    ret
  }
}
