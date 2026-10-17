// Textual ilasm source for the static-fields differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'static-fields' { }
.module 'static-fields.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // static int32 field: store, then read back and add one
    ldc.i4 41
    stsfld int32 Store::count
    ldsfld int32 Store::count
    ldc.i4.1
    add
    call void [mscorlib]System.Console::WriteLine(int32)
    // static string field: store a literal, then write it
    ldstr "hello"
    stsfld string Store::label
    ldsfld string Store::label
    call void [mscorlib]System.Console::WriteLine(string)
    // a static field of an external type, String.Empty, which is an empty line
    ldsfld string [mscorlib]System.String::Empty
    call void [mscorlib]System.Console::WriteLine(string)
    // a static field of this module's own class type, which starts null
    ldnull
    stsfld class Store Store::next
    ldsfld class Store Store::next
    ldnull
    ceq
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public auto ansi Store
{
  .field public static int32 count
  .field public static string label
  .field public static class Store next
  .field public int32 weight
}
