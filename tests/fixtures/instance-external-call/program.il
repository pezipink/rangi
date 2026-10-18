// Textual ilasm source for the instance-external-call differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly 'instance-external-call' { }
.module 'instance-external-call.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    // instance keyword: non-virtual call to an external instance method, receiver first; prints 5
    ldstr "hello"
    call instance int32 [mscorlib]System.String::get_Length()
    call void [mscorlib]System.Console::WriteLine(int32)
    // callvirt needs no keyword; prints 2
    ldstr "hi"
    callvirt instance int32 [mscorlib]System.String::get_Length()
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}
