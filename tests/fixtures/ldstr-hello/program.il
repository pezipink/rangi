// Textual ilasm source for the ldstr-hello differential check. It mirrors program.rktd.
// The entry point sits on Program rather than <Module>, because the CLR rejects entry points
// declared on <Module>; Rangi moves <Module> methods to a generated Program class in the same way.
.assembly extern mscorlib { .ver 4:0:0:0 }
.assembly donothing { }
.module 'ldstr-hello.exe'

.class private auto ansi Program
{
  .method public static void main() cil managed
  {
    .entrypoint
    // A redirected console writes with the OEM code page, which cannot show the non-ASCII
    // literal, so select UTF-8 first.
    call class [mscorlib]System.Text.Encoding [mscorlib]System.Text.Encoding::get_UTF8()
    call void [mscorlib]System.Console::set_OutputEncoding(class [mscorlib]System.Text.Encoding)
    // ASCII literal: one UTF-16 code unit per character
    ldstr "Hello, world"
    call void [mscorlib]System.Console::WriteLine(string)
    // "Grüße, 世界 😀" as UTF-16LE bytes: U+00FC, U+00DF (BMP), U+4E16 U+754C (CJK), and
    // U+1F600 as the surrogate pair D83D DE00. ilasm does not decode \u escapes in strings.
    ldstr bytearray (47 00 72 00 FC 00 DF 00 65 00 2C 00 20 00 16 4E 4C 75 20 00 3D D8 00 DE)
    dup
    call void [mscorlib]System.Console::WriteLine(string)
    // 11 code points but 12 UTF-16 code units, because U+1F600 is a surrogate pair
    callvirt instance int32 [mscorlib]System.String::get_Length()
    call void [mscorlib]System.Console::WriteLine(int32)
    ret
  }
}
