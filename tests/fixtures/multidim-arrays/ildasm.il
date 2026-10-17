
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
// Characteristics:            0x0102
// ----- PE Optional Header (32 bit):
// Magic:                          0x010b
// Major linker version:           0x06
// Minor linker version:           0x05
// Size of code:                   0x00000400
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x0000235c
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
// 0x00002310 [0x00000028] address [size] of Import Directory:          
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
//              0x00000362 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x0000035e
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000234e Import Name Table
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
//              0x000000dc Size
//              '#~' Name
//    Stream 2:
//              0x00000148 Offset
//              0x0000008c Size
//              '#Strings' Name
//    Stream 3:
//              0x000001d4 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x000001d8 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000001e8 Offset
//              0x00000040 Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000908020447 MaskValid
//      0x0000000000000000 Sorted

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
// Managed code         : 138               ( 6.74%)
// Data                 : 512               (25.00%)
// Unaccounted          : 118               ( 5.76%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 552
//   Module        -    1 (10 bytes)
//   TypeDef       -    2 (28 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    3 (18 bytes)
//   MethodDef     -    1 (14 bytes)      0 abstract, 0 native, 1 bodies
//   MemberRef     -    7 (42 bytes)
//   StandAloneSig -    1 (2 bytes)
//   TypeSpec      -    1 (2 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   137 bytes
//   Blobs         -    64 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   173 bytes

// CLR method headers : 12
//   Num.of method bodies  - 1
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 0

// Managed code : 138
//   Ave method size - 138
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
.module 'multidim-arrays.exe'
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
    // Code size       138 (0x8a)
    .maxstack  8
    .locals /*11000001*/ init (int32[,] V_0,
             int32 V_1,
             int32 V_2,
             int32 V_3)
    IL_0000:  /* 18   |                  */ ldc.i4.2
    IL_0001:  /* 19   |                  */ ldc.i4.3
    IL_0002:  /* 73   | (0A)000001       */ newobj     instance void int32[,]/*1B000001*/::.ctor(int32,
                                                                                                 int32) /* 0A000001 */
    IL_0007:  /* 0A   |                  */ stloc.0
    IL_0008:  /* 16   |                  */ ldc.i4.0
    IL_0009:  /* 0B   |                  */ stloc.1
    IL_000a:  /* 07   |                  */ ldloc.1
    IL_000b:  /* 18   |                  */ ldc.i4.2
    IL_000c:  /* 2F   | 21               */ bge.s      IL_002f

    IL_000e:  /* 16   |                  */ ldc.i4.0
    IL_000f:  /* 0C   |                  */ stloc.2
    IL_0010:  /* 08   |                  */ ldloc.2
    IL_0011:  /* 19   |                  */ ldc.i4.3
    IL_0012:  /* 2F   | 15               */ bge.s      IL_0029

    IL_0014:  /* 06   |                  */ ldloc.0
    IL_0015:  /* 07   |                  */ ldloc.1
    IL_0016:  /* 08   |                  */ ldloc.2
    IL_0017:  /* 07   |                  */ ldloc.1
    IL_0018:  /* 19   |                  */ ldc.i4.3
    IL_0019:  /* 5A   |                  */ mul
    IL_001a:  /* 08   |                  */ ldloc.2
    IL_001b:  /* 58   |                  */ add
    IL_001c:  /* 17   |                  */ ldc.i4.1
    IL_001d:  /* 58   |                  */ add
    IL_001e:  /* 28   | (0A)000002       */ call       instance void int32[,]/*1B000001*/::Set(int32,
                                                                                               int32,
                                                                                               int32) /* 0A000002 */
    IL_0023:  /* 08   |                  */ ldloc.2
    IL_0024:  /* 17   |                  */ ldc.i4.1
    IL_0025:  /* 58   |                  */ add
    IL_0026:  /* 0C   |                  */ stloc.2
    IL_0027:  /* 2B   | E7               */ br.s       IL_0010

    IL_0029:  /* 07   |                  */ ldloc.1
    IL_002a:  /* 17   |                  */ ldc.i4.1
    IL_002b:  /* 58   |                  */ add
    IL_002c:  /* 0B   |                  */ stloc.1
    IL_002d:  /* 2B   | DB               */ br.s       IL_000a

    IL_002f:  /* 16   |                  */ ldc.i4.0
    IL_0030:  /* 0D   |                  */ stloc.3
    IL_0031:  /* 16   |                  */ ldc.i4.0
    IL_0032:  /* 0B   |                  */ stloc.1
    IL_0033:  /* 07   |                  */ ldloc.1
    IL_0034:  /* 18   |                  */ ldc.i4.2
    IL_0035:  /* 2F   | 1D               */ bge.s      IL_0054

    IL_0037:  /* 16   |                  */ ldc.i4.0
    IL_0038:  /* 0C   |                  */ stloc.2
    IL_0039:  /* 08   |                  */ ldloc.2
    IL_003a:  /* 19   |                  */ ldc.i4.3
    IL_003b:  /* 2F   | 11               */ bge.s      IL_004e

    IL_003d:  /* 09   |                  */ ldloc.3
    IL_003e:  /* 06   |                  */ ldloc.0
    IL_003f:  /* 07   |                  */ ldloc.1
    IL_0040:  /* 08   |                  */ ldloc.2
    IL_0041:  /* 28   | (0A)000003       */ call       instance int32 int32[,]/*1B000001*/::Get(int32,
                                                                                                int32) /* 0A000003 */
    IL_0046:  /* 58   |                  */ add
    IL_0047:  /* 0D   |                  */ stloc.3
    IL_0048:  /* 08   |                  */ ldloc.2
    IL_0049:  /* 17   |                  */ ldc.i4.1
    IL_004a:  /* 58   |                  */ add
    IL_004b:  /* 0C   |                  */ stloc.2
    IL_004c:  /* 2B   | EB               */ br.s       IL_0039

    IL_004e:  /* 07   |                  */ ldloc.1
    IL_004f:  /* 17   |                  */ ldc.i4.1
    IL_0050:  /* 58   |                  */ add
    IL_0051:  /* 0B   |                  */ stloc.1
    IL_0052:  /* 2B   | DF               */ br.s       IL_0033

    IL_0054:  /* 09   |                  */ ldloc.3
    IL_0055:  /* 28   | (0A)000004       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000004 */
    IL_005a:  /* 06   |                  */ ldloc.0
    IL_005b:  /* 16   |                  */ ldc.i4.0
    IL_005c:  /* 17   |                  */ ldc.i4.1
    IL_005d:  /* 28   | (0A)000005       */ call       instance int32& int32[,]/*1B000001*/::Address(int32,
                                                                                                     int32) /* 0A000005 */
    IL_0062:  /* 1F   | 2A               */ ldc.i4.s   42
    IL_0064:  /* 54   |                  */ stind.i4
    IL_0065:  /* 06   |                  */ ldloc.0
    IL_0066:  /* 16   |                  */ ldc.i4.0
    IL_0067:  /* 17   |                  */ ldc.i4.1
    IL_0068:  /* 28   | (0A)000003       */ call       instance int32 int32[,]/*1B000001*/::Get(int32,
                                                                                                int32) /* 0A000003 */
    IL_006d:  /* 28   | (0A)000004       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000004 */
    IL_0072:  /* 06   |                  */ ldloc.0
    IL_0073:  /* 28   | (0A)000006       */ call       instance int32 [mscorlib/*23000001*/]System.Array/*01000003*/::get_Rank() /* 0A000006 */
    IL_0078:  /* 28   | (0A)000004       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000004 */
    IL_007d:  /* 06   |                  */ ldloc.0
    IL_007e:  /* 17   |                  */ ldc.i4.1
    IL_007f:  /* 28   | (0A)000007       */ call       instance int32 [mscorlib/*23000001*/]System.Array/*01000003*/::GetLength(int32) /* 0A000007 */
    IL_0084:  /* 28   | (0A)000004       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000004 */
    IL_0089:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
