// Textual ilasm source for the asm-refs-versioned differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>.
.assembly extern mscorlib { .ver 4:0:0:0 .publickeytoken = (B7 7A 5C 56 19 34 E0 89) }
.assembly extern System { .ver 4:0:0:0 .publickeytoken = (B7 7A 5C 56 19 34 E0 89) }
.assembly 'asm-refs-versioned' { }
.module 'asm-refs-versioned.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    .maxstack 8
    // a type from System: a string is not a Regex, so isinst gives null and ceq gives 1
    ldstr "abc"
    isinst [System]System.Text.RegularExpressions.Regex
    ldnull
    ceq
    call void [mscorlib]System.Console::WriteLine(int32)
    // a method from System: Regex.IsMatch is true for "b+" in "abc"
    ldstr "abc"
    ldstr "b+"
    call bool [System]System.Text.RegularExpressions.Regex::IsMatch(string, string)
    call void [mscorlib]System.Console::WriteLine(bool)
    ret
  }
}
