
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
// Addr. of entry point:           0x00002324
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
// 0x000022d8 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00004000 [0x0000000c] address [size] of Base Relocation Table:     
// 0x00000000 [0x00000000] address [size] of Debug Directory:           
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
//              0x0000032a Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x00000326
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00002316 Import Name Table
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
// 0x00002050 [0x00000228] address [size] of Metadata Directory:        
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
//              0x00000114 Size
//              '#~' Name
//    Stream 2:
//              0x00000180 Offset
//              0x0000007c Size
//              '#Strings' Name
//    Stream 3:
//              0x000001fc Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000200 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000210 Offset
//              0x00000018 Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x000000090003a457 MaskValid
//      0x000000000001a000 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2048
// PE header size       : 512 (456 used)    (25.00%)
// PE additional info   : 132               ( 6.45%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 3.52%)
// CLR meta-data size  : 552                (26.95%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 12                 ( 0.59%)
// Managed code         : 83                ( 4.05%)
// Data                 : 512               (25.00%)
// Unaccounted          : 173               ( 8.45%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 552
//   Module        -    1 (10 bytes)
//   TypeDef       -    4 (56 bytes)      0 interfaces, 1 explicit layout
//   TypeRef       -    3 (18 bytes)
//   MethodDef     -    1 (14 bytes)      0 abstract, 0 native, 1 bodies
//   FieldDef      -    4 (24 bytes)      0 constant
//   MemberRef     -    1 (6 bytes)
//   NativeType    -    1 (4 bytes)
//   ClassLayout   -    2 (16 bytes)
//   FieldLayout   -    2 (12 bytes)
//   StandAloneSig -    1 (2 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   122 bytes
//   Blobs         -    24 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   182 bytes

// CLR method headers : 12
//   Num.of method bodies  - 1
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 0

// Managed code : 83
//   Ave method size - 83
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class Overlay                        (public) (explicit) (ansi) (sealed) 
// Class Packed                         (public) (sequential) (ansi) (sealed) 
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
.module 'class-layout.exe'
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
    // Method begins at RVA 0x2278
    // Code size       83 (0x53)
    .maxstack  8
    .locals /*11000001*/ init (valuetype Overlay/*02000003*/ V_0,
             valuetype Packed/*02000004*/ V_1)
    IL_0000:  /* 12   | 00               */ ldloca.s   V_0
    IL_0002:  /* 1D   |                  */ ldc.i4.7
    IL_0003:  /* 7D   | (04)000001       */ stfld      int32 Overlay/*02000003*/::lo /* 04000001 */
    IL_0008:  /* 12   | 00               */ ldloca.s   V_0
    IL_000a:  /* 1F   | 23               */ ldc.i4.s   35
    IL_000c:  /* 7D   | (04)000002       */ stfld      int32 Overlay/*02000003*/::hi /* 04000002 */
    IL_0011:  /* 12   | 00               */ ldloca.s   V_0
    IL_0013:  /* 7B   | (04)000001       */ ldfld      int32 Overlay/*02000003*/::lo /* 04000001 */
    IL_0018:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_001d:  /* 12   | 00               */ ldloca.s   V_0
    IL_001f:  /* 7B   | (04)000002       */ ldfld      int32 Overlay/*02000003*/::hi /* 04000002 */
    IL_0024:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0029:  /* 12   | 01               */ ldloca.s   V_1
    IL_002b:  /* 1F   | 28               */ ldc.i4.s   40
    IL_002d:  /* 7D   | (04)000003       */ stfld      int32 Packed/*02000004*/::a /* 04000003 */
    IL_0032:  /* 12   | 01               */ ldloca.s   V_1
    IL_0034:  /* 18   |                  */ ldc.i4.2
    IL_0035:  /* 7D   | (04)000004       */ stfld      int32 Packed/*02000004*/::b /* 04000004 */
    IL_003a:  /* 12   | 01               */ ldloca.s   V_1
    IL_003c:  /* 7B   | (04)000003       */ ldfld      int32 Packed/*02000004*/::a /* 04000003 */
    IL_0041:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0046:  /* 12   | 01               */ ldloca.s   V_1
    IL_0048:  /* 7B   | (04)000004       */ ldfld      int32 Packed/*02000004*/::b /* 04000004 */
    IL_004d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0052:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public explicit ansi sealed Overlay
       extends [mscorlib/*23000001*/]System.ValueType/*01000003*/
{
  .pack 4
  .size 8
  .field /*04000001*/ [0] public int32 lo
  .field /*04000002*/ [4] public int32 hi
} // end of class Overlay

.class /*02000004*/ public sequential ansi sealed Packed
       extends [mscorlib/*23000001*/]System.ValueType/*01000003*/
{
  .pack 2
  .size 12
  .field /*04000003*/ public int32 a
  .field /*04000004*/ public  marshal( int32) int32 b
} // end of class Packed


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
