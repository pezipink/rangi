
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
// Size of code:                   0x00000400
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x000022e4
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
// 0x00002298 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00004000 [0x0000000c] address [size] of Base Relocation Table:     
// 0x000022ec [0x00000054] address [size] of Debug Directory:           
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
//              0x0000038b Virtual Size
//              0x00002000 Virtual Address
//              0x00000400 Size of Raw Data
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
//              0x00000600 Pointer to Raw Data
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
//              Entry 1: Type 0x3 Offset 0x000002e6
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x000022d6 Import Name Table
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
// 0x00002050 [0x000001d0] address [size] of Metadata Directory:        
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
//              0x000000d0 Size
//              '#~' Name
//    Stream 2:
//              0x0000013c Offset
//              0x00000064 Size
//              '#Strings' Name
//    Stream 3:
//              0x000001a0 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x000001a4 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000001b4 Offset
//              0x0000001c Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000900020447 MaskValid
//      0x0000000000000000 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2048
// PE header size       : 512 (456 used)    (25.00%)
// PE additional info   : 216               (10.55%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 3.52%)
// CLR meta-data size  : 464                (22.66%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 25                 ( 1.22%)
// Managed code         : 94                ( 4.59%)
// Data                 : 512               (25.00%)
// Unaccounted          : 153               ( 7.47%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 464
//   Module        -    1 (10 bytes)
//   TypeDef       -    2 (28 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    3 (18 bytes)
//   MethodDef     -    3 (42 bytes)      0 abstract, 0 native, 3 bodies
//   MemberRef     -    1 (6 bytes)
//   StandAloneSig -    2 (4 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   100 bytes
//   Blobs         -    28 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   166 bytes

// CLR method headers : 25
//   Num.of method bodies  - 3
//   Num.of fat headers    - 2
//   Num.of tiny headers   - 1

// Managed code : 94
//   Ave method size - 31
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
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
.module 'arrays-sum.exe'
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
    // Method begins at RVA 0x2220
    // Code size       63 (0x3f)
    .maxstack  8
    .locals /*11000001*/ init (int32[] V_0,
             int32 V_1)
    IL_0000:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0002:  /* 8D   | (01)000002       */ newarr     [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0007:  /* 0A   |                  */ stloc.0
    IL_0008:  /* 16   |                  */ ldc.i4.0
    IL_0009:  /* 0B   |                  */ stloc.1
    IL_000a:  /* 07   |                  */ ldloc.1
    IL_000b:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_000d:  /* 2F   | 10               */ bge.s      IL_001f

    IL_000f:  /* 06   |                  */ ldloc.0
    IL_0010:  /* 07   |                  */ ldloc.1
    IL_0011:  /* 07   |                  */ ldloc.1
    IL_0012:  /* 07   |                  */ ldloc.1
    IL_0013:  /* 5A   |                  */ mul
    IL_0014:  /* A4   | (01)000002       */ stelem     [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0019:  /* 07   |                  */ ldloc.1
    IL_001a:  /* 17   |                  */ ldc.i4.1
    IL_001b:  /* 58   |                  */ add
    IL_001c:  /* 0B   |                  */ stloc.1
    IL_001d:  /* 2B   | EB               */ br.s       IL_000a

    IL_001f:  /* 06   |                  */ ldloc.0
    IL_0020:  /* 28   | (06)000003       */ call       int32 Program/*02000002*/::sum(int32[]) /* 06000003 */
    IL_0025:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_002a:  /* 06   |                  */ ldloc.0
    IL_002b:  /* 19   |                  */ ldc.i4.3
    IL_002c:  /* A3   | (01)000002       */ ldelem     [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0031:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_0036:  /* 06   |                  */ ldloc.0
    IL_0037:  /* 8E   |                  */ ldlen
    IL_0038:  /* 69   |                  */ conv.i4
    IL_0039:  /* 28   | (06)000002       */ call       void Program/*02000002*/::show(int32) /* 06000002 */
    IL_003e:  /* 2A   |                  */ ret
  } // end of method Program::main

  .method /*06000002*/ public static void 
          show(int32 A_0) cil managed
  // SIG: 00 01 01 08
  {
    // Method begins at RVA 0x226c
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Program::show

  .method /*06000003*/ public static int32 
          sum(int32[] A_0) cil managed
  // SIG: 00 01 08 1D 08
  {
    // Method begins at RVA 0x2274
    // Code size       24 (0x18)
    .maxstack  8
    .locals /*11000002*/ init (int32 V_0,
             int32 V_1)
    IL_0000:  /* 16   |                  */ ldc.i4.0
    IL_0001:  /* 0A   |                  */ stloc.0
    IL_0002:  /* 16   |                  */ ldc.i4.0
    IL_0003:  /* 0B   |                  */ stloc.1
    IL_0004:  /* 07   |                  */ ldloc.1
    IL_0005:  /* 02   |                  */ ldarg.0
    IL_0006:  /* 8E   |                  */ ldlen
    IL_0007:  /* 69   |                  */ conv.i4
    IL_0008:  /* 2F   | 0C               */ bge.s      IL_0016

    IL_000a:  /* 06   |                  */ ldloc.0
    IL_000b:  /* 02   |                  */ ldarg.0
    IL_000c:  /* 07   |                  */ ldloc.1
    IL_000d:  /* 94   |                  */ ldelem.i4
    IL_000e:  /* 58   |                  */ add
    IL_000f:  /* 0A   |                  */ stloc.0
    IL_0010:  /* 07   |                  */ ldloc.1
    IL_0011:  /* 17   |                  */ ldc.i4.1
    IL_0012:  /* 58   |                  */ add
    IL_0013:  /* 0B   |                  */ stloc.1
    IL_0014:  /* 2B   | EE               */ br.s       IL_0004

    IL_0016:  /* 06   |                  */ ldloc.0
    IL_0017:  /* 2A   |                  */ ret
  } // end of method Program::sum

} // end of class Program


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
