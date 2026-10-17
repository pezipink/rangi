
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
// Size of code:                   0x00000600
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x00002480
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
// 0x00002434 [0x00000028] address [size] of Import Directory:          
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
//              0x00000486 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x00000482
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00002472 Import Name Table
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
// 0x00002050 [0x000001fc] address [size] of Metadata Directory:        
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
//              0x000000f8 Size
//              '#~' Name
//    Stream 2:
//              0x00000164 Offset
//              0x00000074 Size
//              '#Strings' Name
//    Stream 3:
//              0x000001d8 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x000001dc Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000001ec Offset
//              0x00000010 Size
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
// PE additional info   : 132               ( 5.16%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 2.81%)
// CLR meta-data size  : 508                (19.84%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 38                 ( 1.48%)
// Managed code         : 437               (17.07%)
// Data                 : 512               (20.00%)
// Unaccounted          : 349               (13.63%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 508
//   Module        -    1 (10 bytes)
//   TypeDef       -    4 (56 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    5 (70 bytes)      0 abstract, 0 native, 5 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   114 bytes
//   Blobs         -    16 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   162 bytes

// CLR method headers : 38
//   Num.of method bodies  - 5
//   Num.of fat headers    - 3
//   Num.of tiny headers   - 2

// Managed code : 437
//   Ave method size - 87
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class T0                             (public) (auto) (ansi) 
// Class T1                             (public) (auto) (ansi) 
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
.module 'text-over-400.exe'
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
    // Method begins at RVA 0x224c
    // Code size       245 (0xf5)
    .maxstack  2
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 20   | 05000000         */ ldc.i4     0x5
    IL_001c:  /* 58   |                  */ add
    IL_001d:  /* 20   | 06000000         */ ldc.i4     0x6
    IL_0022:  /* 58   |                  */ add
    IL_0023:  /* 20   | 07000000         */ ldc.i4     0x7
    IL_0028:  /* 58   |                  */ add
    IL_0029:  /* 20   | 08000000         */ ldc.i4     0x8
    IL_002e:  /* 58   |                  */ add
    IL_002f:  /* 20   | 09000000         */ ldc.i4     0x9
    IL_0034:  /* 58   |                  */ add
    IL_0035:  /* 20   | 0A000000         */ ldc.i4     0xa
    IL_003a:  /* 58   |                  */ add
    IL_003b:  /* 20   | 0B000000         */ ldc.i4     0xb
    IL_0040:  /* 58   |                  */ add
    IL_0041:  /* 20   | 0C000000         */ ldc.i4     0xc
    IL_0046:  /* 58   |                  */ add
    IL_0047:  /* 20   | 0D000000         */ ldc.i4     0xd
    IL_004c:  /* 58   |                  */ add
    IL_004d:  /* 20   | 0E000000         */ ldc.i4     0xe
    IL_0052:  /* 58   |                  */ add
    IL_0053:  /* 20   | 0F000000         */ ldc.i4     0xf
    IL_0058:  /* 58   |                  */ add
    IL_0059:  /* 20   | 10000000         */ ldc.i4     0x10
    IL_005e:  /* 58   |                  */ add
    IL_005f:  /* 20   | 11000000         */ ldc.i4     0x11
    IL_0064:  /* 58   |                  */ add
    IL_0065:  /* 20   | 12000000         */ ldc.i4     0x12
    IL_006a:  /* 58   |                  */ add
    IL_006b:  /* 20   | 13000000         */ ldc.i4     0x13
    IL_0070:  /* 58   |                  */ add
    IL_0071:  /* 20   | 14000000         */ ldc.i4     0x14
    IL_0076:  /* 58   |                  */ add
    IL_0077:  /* 20   | 15000000         */ ldc.i4     0x15
    IL_007c:  /* 58   |                  */ add
    IL_007d:  /* 20   | 16000000         */ ldc.i4     0x16
    IL_0082:  /* 58   |                  */ add
    IL_0083:  /* 20   | 17000000         */ ldc.i4     0x17
    IL_0088:  /* 58   |                  */ add
    IL_0089:  /* 20   | 18000000         */ ldc.i4     0x18
    IL_008e:  /* 58   |                  */ add
    IL_008f:  /* 20   | 19000000         */ ldc.i4     0x19
    IL_0094:  /* 58   |                  */ add
    IL_0095:  /* 20   | 1A000000         */ ldc.i4     0x1a
    IL_009a:  /* 58   |                  */ add
    IL_009b:  /* 20   | 1B000000         */ ldc.i4     0x1b
    IL_00a0:  /* 58   |                  */ add
    IL_00a1:  /* 20   | 1C000000         */ ldc.i4     0x1c
    IL_00a6:  /* 58   |                  */ add
    IL_00a7:  /* 20   | 1D000000         */ ldc.i4     0x1d
    IL_00ac:  /* 58   |                  */ add
    IL_00ad:  /* 20   | 1E000000         */ ldc.i4     0x1e
    IL_00b2:  /* 58   |                  */ add
    IL_00b3:  /* 20   | 1F000000         */ ldc.i4     0x1f
    IL_00b8:  /* 58   |                  */ add
    IL_00b9:  /* 20   | 20000000         */ ldc.i4     0x20
    IL_00be:  /* 58   |                  */ add
    IL_00bf:  /* 20   | 21000000         */ ldc.i4     0x21
    IL_00c4:  /* 58   |                  */ add
    IL_00c5:  /* 20   | 22000000         */ ldc.i4     0x22
    IL_00ca:  /* 58   |                  */ add
    IL_00cb:  /* 20   | 23000000         */ ldc.i4     0x23
    IL_00d0:  /* 58   |                  */ add
    IL_00d1:  /* 20   | 24000000         */ ldc.i4     0x24
    IL_00d6:  /* 58   |                  */ add
    IL_00d7:  /* 20   | 25000000         */ ldc.i4     0x25
    IL_00dc:  /* 58   |                  */ add
    IL_00dd:  /* 20   | 26000000         */ ldc.i4     0x26
    IL_00e2:  /* 58   |                  */ add
    IL_00e3:  /* 20   | 27000000         */ ldc.i4     0x27
    IL_00e8:  /* 58   |                  */ add
    IL_00e9:  /* 20   | 28000000         */ ldc.i4     0x28
    IL_00ee:  /* 58   |                  */ add
    IL_00ef:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00f4:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public auto ansi T0
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000002*/ public static int32 
          M0_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2350
    // Code size       18 (0x12)
    .maxstack  9
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 2A   |                  */ ret
  } // end of method T0::M0_0

  .method /*06000003*/ public static int32 
          M0_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2370
    // Code size       36 (0x24)
    .maxstack  8
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 20   | 05000000         */ ldc.i4     0x5
    IL_001c:  /* 58   |                  */ add
    IL_001d:  /* 20   | 06000000         */ ldc.i4     0x6
    IL_0022:  /* 58   |                  */ add
    IL_0023:  /* 2A   |                  */ ret
  } // end of method T0::M0_1

} // end of class T0

.class /*02000004*/ public auto ansi T1
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000004*/ public static int32 
          M1_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2398
    // Code size       60 (0x3c)
    .maxstack  8
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 20   | 05000000         */ ldc.i4     0x5
    IL_001c:  /* 58   |                  */ add
    IL_001d:  /* 20   | 06000000         */ ldc.i4     0x6
    IL_0022:  /* 58   |                  */ add
    IL_0023:  /* 20   | 07000000         */ ldc.i4     0x7
    IL_0028:  /* 58   |                  */ add
    IL_0029:  /* 20   | 08000000         */ ldc.i4     0x8
    IL_002e:  /* 58   |                  */ add
    IL_002f:  /* 20   | 09000000         */ ldc.i4     0x9
    IL_0034:  /* 58   |                  */ add
    IL_0035:  /* 20   | 0A000000         */ ldc.i4     0xa
    IL_003a:  /* 58   |                  */ add
    IL_003b:  /* 2A   |                  */ ret
  } // end of method T1::M1_0

  .method /*06000005*/ public static int32 
          M1_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x23d8
    // Code size       78 (0x4e)
    .maxstack  2
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 20   | 05000000         */ ldc.i4     0x5
    IL_001c:  /* 58   |                  */ add
    IL_001d:  /* 20   | 06000000         */ ldc.i4     0x6
    IL_0022:  /* 58   |                  */ add
    IL_0023:  /* 20   | 07000000         */ ldc.i4     0x7
    IL_0028:  /* 58   |                  */ add
    IL_0029:  /* 20   | 08000000         */ ldc.i4     0x8
    IL_002e:  /* 58   |                  */ add
    IL_002f:  /* 20   | 09000000         */ ldc.i4     0x9
    IL_0034:  /* 58   |                  */ add
    IL_0035:  /* 20   | 0A000000         */ ldc.i4     0xa
    IL_003a:  /* 58   |                  */ add
    IL_003b:  /* 20   | 0B000000         */ ldc.i4     0xb
    IL_0040:  /* 58   |                  */ add
    IL_0041:  /* 20   | 0C000000         */ ldc.i4     0xc
    IL_0046:  /* 58   |                  */ add
    IL_0047:  /* 20   | 0D000000         */ ldc.i4     0xd
    IL_004c:  /* 58   |                  */ add
    IL_004d:  /* 2A   |                  */ ret
  } // end of method T1::M1_1

} // end of class T1


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
