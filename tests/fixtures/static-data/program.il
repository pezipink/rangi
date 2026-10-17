// Textual ilasm source for the static-data differential check. It mirrors program.rktd.
// Static fields with initial data (II.22.18 FieldRVA) are read with ldsfld and printed. The
// entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'static-data' { }
.module 'static-data.exe'

// initial data blocks (II.16); each is named by the field that uses it
.data D_First = bytearray (01 00 00 00)
.data D_Second = bytearray (10 00 00 00)
.data D_Third = bytearray (2A 00 00 00)

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // data 01 00 00 00 reads as the little-endian int32 1
    ldsfld int32 Table::First
    call void [mscorlib]System.Console::WriteLine(int32)
    // a field with no data is zero-initialised
    ldsfld int32 Table::Plain
    call void [mscorlib]System.Console::WriteLine(int32)
    // the byte 10 is hex, so it is sixteen
    ldsfld int32 Table::Second
    call void [mscorlib]System.Console::WriteLine(int32)
    // the byte 2A is hex, so it is forty-two
    ldsfld int32 Table::Third
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}

.class public auto ansi Table
{
  .field public static int32 First at D_First
  .field public static int32 Plain
  .field public static int32 Second at D_Second
  .field public static int32 Third at D_Third
}
