
//  Microsoft (R) .NET Framework IL Disassembler.  Version 4.6.1055.0
//  Copyright (c) Microsoft Corporation.  All rights reserved.


// ----- DOS Header:
// Magic:                      0x5a4d
// Bytes on last page:         0x0090
// Pages in file:              0x0003
// Relocations:                0x0000
// Size of header (paragraphs):0x0004
// Min extra paragraphs:       0x0000
// Max extra paragraphs:       0xffff
// Initial (relative) SS:      0x0000
// Initial SP:                 0x00b8
// Checksum:                   0x0000
// Initial IP:                 0x0000
// Initial (relative) CS:      0x0000
// File addr. of reloc table:  0x0040
// Overlay number:             0x0000
// OEM identifier:             0x0000
// OEM info:                   0x0000
// File addr. of COFF header:  0x0080
// ----- COFF/PE Headers:
// Signature:                  0x00004550
// ----- COFF Header:
// Machine:                    0x014c
// Number of sections:         0x0002
// Time-date stamp:            0x00000000
// Ptr to symbol table:        0x00000000
// Number of symbols:          0x00000000
// Size of optional header:    0x00e0
// Characteristics:            0x0002
// ----- PE Optional Header (32 bit):
// Magic:                          0x010b
// Major linker version:           0x06
// Minor linker version:           0x05
// Size of code:                   0x00000600
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x0000239c
// Base of code:                   0x00002000
// Base of data:                   0x00004000
// Section alignment:              0x00002000
// File alignment:                 0x00000200
// Major OS version:               0x0004
// Minor OS version:               0x0000
// Major image version:            0x0000
// Minor image version:            0x0000
// Major subsystem version:        0x0004
// Minor subsystem version:        0x0000
// Size of image:                  0x00006000
// Size of headers:                0x00000200
// Checksum:                       0x00000000
// Subsystem:                      0x0003
// DLL characteristics:            0x8540
// Size of stack reserve:          0x00100000
// Size of stack commit:           0x00001000
// Size of heap reserve:           0x00100000
// Size of heap commit:            0x00001000
// Loader flags:                   0x00000000
// Directories:                    0x00000010
// 0x00000000 [0x00000000] address [size] of Export Directory:          
// 0x00002350 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00004000 [0x0000000c] address [size] of Base Relocation Table:     
// 0x000023a4 [0x00000054] address [size] of Debug Directory:           
// 0x00000000 [0x00000000] address [size] of Architecture Specific:     
// 0x00000000 [0x00000000] address [size] of Global Pointer:            
// 0x00000000 [0x00000000] address [size] of TLS Directory:             
// 0x00000000 [0x00000000] address [size] of Load Config Directory:     
// 0x00000000 [0x00000000] address [size] of Bound Import Directory:    
// 0x00002000 [0x00000008] address [size] of Import Address Table:      
// 0x00000000 [0x00000000] address [size] of Delay Load IAT:            
// 0x00002008 [0x00000048] address [size] of CLR Header:                


// Image sections:
//              .text
//              0x00000443 Virtual Size
//              0x00002000 Virtual Address
//              0x00000600 Size of Raw Data
//              0x00000200 Pointer to Raw Data
//              0x00000000 Pointer to Relocations
//              0x00000000 Pointer to Linenumbers
//                  0x0000 Number of Relocations
//                  0x0000 Number of Linenumbers
//              0x60000020 Characteristics
//                         CNT_CODE
//                         MEM_EXECUTE
//                         MEM_READ

//              .reloc
//              0x0000000c Virtual Size
//              0x00004000 Virtual Address
//              0x00000200 Size of Raw Data
//              0x00000800 Pointer to Raw Data
//              0x00000000 Pointer to Relocations
//              0x00000000 Pointer to Linenumbers
//                  0x0000 Number of Relocations
//                  0x0000 Number of Linenumbers
//              0x42000040 Characteristics
//                         CNT_INITIALIZED_DATA
//                         MEM_DISCARDABLE
//                         MEM_READ

// Base Relocation Table
//              0x00002000 Page RVA
//              0x0000000c Block Size
//              0x00000002 Number of Entries
//              Entry 1: Type 0x3 Offset 0x0000039e
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000238e Import Name Table
//              0          Time Date Stamp
//              0          Index of First Forwarder Reference
//
//              0x0000  _CorExeMain

// Delay Load Import Address Table
// No data.

// Entry point code:
//FF 25 00 20 40 00 


// ----- CLR Header:
// Header size:                        0x00000048
// Major runtime version:              0x0002
// Minor runtime version:              0x0000
// 0x00002050 [0x00000248] address [size] of Metadata Directory:        
// Flags:                              0x00000001
// Entry point token:                  0x06000001
// 0x00000000 [0x00000000] address [size] of Resources Directory:       
// 0x00000000 [0x00000000] address [size] of Strong Name Signature:     
// 0x00000000 [0x00000000] address [size] of CodeManager Table:         
// 0x00000000 [0x00000000] address [size] of VTableFixups Directory:    
// 0x00000000 [0x00000000] address [size] of Export Address Table:      
// 0x00000000 [0x00000000] address [size] of Precompile Header:         

// Metadata Header
//    Storage Signature:
//              0x424a5342 Signature
//                  0x0001 Major Version
//                  0x0001 Minor Version
//              0x00000000 Extra Data Offset
//              0x0000000c Version String Length
//              'v4.0.30319' Version String
//    Storage Header:
//                    0x00 Flags
//                  0x0005 Number of Streams
//    Stream 1:
//              0x0000006c Offset
//              0x00000124 Size
//              '#~' Name
//    Stream 2:
//              0x00000190 Offset
//              0x00000088 Size
//              '#Strings' Name
//    Stream 3:
//              0x00000218 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x0000021c Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x0000022c Offset
//              0x0000001c Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000900000447 MaskValid
//      0x0000000000000000 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2560
// PE header size       : 512 (456 used)    (20.00%)
// PE additional info   : 216               ( 8.44%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 2.81%)
// CLR meta-data size  : 584                (22.81%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 20                 ( 0.78%)
// Managed code         : 146               ( 5.70%)
// Data                 : 512               (20.00%)
// Unaccounted          : 498               (19.45%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 584
//   Module        -    1 (10 bytes)
//   TypeDef       -    3 (42 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    9 (126 bytes)     0 abstract, 0 native, 9 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   133 bytes
//   Blobs         -    28 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   165 bytes

// CLR method headers : 20
//   Num.of method bodies  - 9
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 8

// Managed code : 146
//   Ave method size - 16
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class Util                           (auto) (ansi) 
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


// Metadata version: v4.0.30319
.assembly extern /*23000001*/ mscorlib
{
  .ver 0:0:0:0
}
.assembly /*20000001*/ image
{
  .ver 0:0:0:0
}
.module 'calls-multi.exe'
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003       // WINDOWS_CUI
.corflags 0x00000001    //  ILONLY


// =============== CLASS MEMBERS DECLARATION ===================

.class /*02000002*/ private auto ansi Program
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000001*/ public static void 
          main() cil managed
  // SIG: 00 00 01
  {
    .entrypoint
    // Method begins at RVA 0x2298
    // Code size       68 (0x44)
    .maxstack  8
    IL_0000:  /* 28   | (06)000003       */ call       int32 Program/*02000002*/::seven() /* 06000003 */
    IL_0005:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_000a:  /* 1B   |                  */ ldc.i4.5
    IL_000b:  /* 28   | (06)000008       */ call       int32 Program/*02000002*/::fact(int32) /* 06000008 */
    IL_0010:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_0015:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0017:  /* 28   | (06)000007       */ call       int32 Program/*02000002*/::fib(int32) /* 06000007 */
    IL_001c:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_0021:  /* 19   |                  */ ldc.i4.3
    IL_0022:  /* 28   | (06)000004       */ call       int32 Program/*02000002*/::quad(int32) /* 06000004 */
    IL_0027:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_002c:  /* 1D   |                  */ ldc.i4.7
    IL_002d:  /* 28   | (06)000009       */ call       int32 Util/*02000003*/::square(int32) /* 06000009 */
    IL_0032:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_0037:  /* 18   |                  */ ldc.i4.2
    IL_0038:  /* 19   |                  */ ldc.i4.3
    IL_0039:  /* 28   | (06)000006       */ call       int32 Program/*02000002*/::'add'(int32,
                                                                                        int32) /* 06000006 */
    IL_003e:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_0043:  /* 2A   |                  */ ret
  } // end of method Program::main

  .method /*06000002*/ public static void 
          show(int32 A_0) cil managed
  // SIG: 00 01 01 08
  {
    // Method begins at RVA 0x22e8
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Program::show

  .method /*06000003*/ public static int32 
          seven() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x22f0
    // Code size       2 (0x2)
    .maxstack  8
    IL_0000:  /* 1D   |                  */ ldc.i4.7
    IL_0001:  /* 2A   |                  */ ret
  } // end of method Program::seven

  .method /*06000004*/ public static int32 
          quad(int32 A_0) cil managed
  // SIG: 00 01 08 08
  {
    // Method begins at RVA 0x22f4
    // Code size       12 (0xc)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (06)000005       */ call       int32 Program/*02000002*/::twice(int32) /* 06000005 */
    IL_0006:  /* 28   | (06)000005       */ call       int32 Program/*02000002*/::twice(int32) /* 06000005 */
    IL_000b:  /* 2A   |                  */ ret
  } // end of method Program::quad

  .method /*06000005*/ public static int32 
          twice(int32 A_0) cil managed
  // SIG: 00 01 08 08
  {
    // Method begins at RVA 0x2304
    // Code size       8 (0x8)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 02   |                  */ ldarg.0
    IL_0002:  /* 28   | (06)000006       */ call       int32 Program/*02000002*/::'add'(int32,
                                                                                        int32) /* 06000006 */
    IL_0007:  /* 2A   |                  */ ret
  } // end of method Program::twice

  .method /*06000006*/ public static int32 
          'add'(int32 A_0,
                int32 A_1) cil managed
  // SIG: 00 02 08 08 08
  {
    // Method begins at RVA 0x2310
    // Code size       4 (0x4)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 03   |                  */ ldarg.1
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 2A   |                  */ ret
  } // end of method Program::'add'

  .method /*06000007*/ public static int32 
          fib(int32 A_0) cil managed
  // SIG: 00 01 08 08
  {
    // Method begins at RVA 0x2318
    // Code size       24 (0x18)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 32   | 12               */ blt.s      IL_0016

    IL_0004:  /* 02   |                  */ ldarg.0
    IL_0005:  /* 17   |                  */ ldc.i4.1
    IL_0006:  /* 59   |                  */ sub
    IL_0007:  /* 28   | (06)000007       */ call       int32 Program/*02000002*/::fib(int32) /* 06000007 */
    IL_000c:  /* 02   |                  */ ldarg.0
    IL_000d:  /* 18   |                  */ ldc.i4.2
    IL_000e:  /* 59   |                  */ sub
    IL_000f:  /* 28   | (06)000007       */ call       int32 Program/*02000002*/::fib(int32) /* 06000007 */
    IL_0014:  /* 58   |                  */ add
    IL_0015:  /* 2A   |                  */ ret

    IL_0016:  /* 02   |                  */ ldarg.0
    IL_0017:  /* 2A   |                  */ ret
  } // end of method Program::fib

  .method /*06000008*/ public static int32 
          fact(int32 A_0) cil managed
  // SIG: 00 01 08 08
  {
    // Method begins at RVA 0x2334
    // Code size       17 (0x11)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 32   | 0B               */ blt.s      IL_000f

    IL_0004:  /* 02   |                  */ ldarg.0
    IL_0005:  /* 02   |                  */ ldarg.0
    IL_0006:  /* 17   |                  */ ldc.i4.1
    IL_0007:  /* 59   |                  */ sub
    IL_0008:  /* 28   | (06)000008       */ call       int32 Program/*02000002*/::fact(int32) /* 06000008 */
    IL_000d:  /* 5A   |                  */ mul
    IL_000e:  /* 2A   |                  */ ret

    IL_000f:  /* 17   |                  */ ldc.i4.1
    IL_0010:  /* 2A   |                  */ ret
  } // end of method Program::fact

} // end of class Program

.class /*02000003*/ private auto ansi Util
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000009*/ public static int32 
          square(int32 A_0) cil managed
  // SIG: 00 01 08 08
  {
    // Method begins at RVA 0x2348
    // Code size       4 (0x4)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 02   |                  */ ldarg.0
    IL_0002:  /* 5A   |                  */ mul
    IL_0003:  /* 2A   |                  */ ret
  } // end of method Util::square

} // end of class Util


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
