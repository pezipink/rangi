// Textual ilasm source for the multi-types fixture. It mirrors program.rktd, and the
// differential test assembles it with ilasm.exe and compares the result with the Rangi image.
.assembly extern mscorlib
{
  .ver 4:0:0:0
}
.assembly 'multi-types'
{
}
.module 'multi-types.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // p = new Geometry.Point(3, 4); p.Sum() is 7
    ldc.i4.3
    ldc.i4.4
    newobj instance void Geometry.Point::.ctor(int32, int32)
    dup
    callvirt instance int32 Geometry.Point::Sum()
    call void [mscorlib]System.Console::WriteLine(int32)
    // h = new Demo.Holder(p); h.item.Sum() is 7 (a class-typed field and parameter)
    newobj instance void Demo.Holder::.ctor(class Geometry.Point)
    ldfld class Geometry.Point Demo.Holder::item
    callvirt instance int32 Geometry.Point::Sum()
    call void [mscorlib]System.Console::WriteLine(int32)
    // q = Geometry.Shapes.Make(10) gives (10, 11), so Sum is 21 (a class-typed return)
    ldc.i4.s 10
    call class Geometry.Point Geometry.Shapes::Make(int32)
    dup
    callvirt instance int32 Geometry.Point::Sum()
    call void [mscorlib]System.Console::WriteLine(int32)
    // Twice(q) is 42
    call int32 Geometry.Shapes::Twice(class Geometry.Point)
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public auto ansi Geometry.Point
{
  .field public int32 x
  .field public int32 y

  .method public specialname rtspecialname instance void .ctor(int32, int32) cil managed
  {
    .maxstack 8
    ldarg.0
    call instance void [mscorlib]System.Object::.ctor()
    ldarg.0
    ldarg.1
    stfld int32 Geometry.Point::x
    ldarg.0
    ldarg.2
    stfld int32 Geometry.Point::y
    ret
  }

  .method public instance int32 Sum() cil managed
  {
    .maxstack 8
    ldarg.0
    ldfld int32 Geometry.Point::x
    ldarg.0
    ldfld int32 Geometry.Point::y
    add
    ret
  }
}

.class public auto ansi Geometry.Shapes
{
  .method public static class Geometry.Point Make(int32) cil managed
  {
    .maxstack 8
    ldarg.0
    ldarg.0
    ldc.i4.1
    add
    newobj instance void Geometry.Point::.ctor(int32, int32)
    ret
  }

  .method public static int32 Twice(class Geometry.Point) cil managed
  {
    .maxstack 8
    ldarg.0
    callvirt instance int32 Geometry.Point::Sum()
    ldc.i4.2
    mul
    ret
  }
}

.class public auto ansi Demo.Holder
{
  .field public class Geometry.Point item

  .method public specialname rtspecialname instance void .ctor(class Geometry.Point) cil managed
  {
    .maxstack 8
    ldarg.0
    call instance void [mscorlib]System.Object::.ctor()
    ldarg.0
    ldarg.1
    stfld class Geometry.Point Demo.Holder::item
    ret
  }
}
