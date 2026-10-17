
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
// Size of code:                   0x00002200
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x00004194
// Base of code:                   0x00002000
// Base of data:                   0x00006000
// Section alignment:              0x00002000
// File alignment:                 0x00000200
// Major OS version:               0x0004
// Minor OS version:               0x0000
// Major image version:            0x0000
// Minor image version:            0x0000
// Major subsystem version:        0x0004
// Minor subsystem version:        0x0000
// Size of image:                  0x00008000
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
// 0x00004148 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00006000 [0x0000000c] address [size] of Base Relocation Table:     
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
//              0x0000219a Virtual Size
//              0x00002000 Virtual Address
//              0x00002200 Size of Raw Data
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
//              0x00006000 Virtual Address
//              0x00000200 Size of Raw Data
//              0x00002400 Pointer to Raw Data
//              0x00000000 Pointer to Relocations
//              0x00000000 Pointer to Linenumbers
//                  0x0000 Number of Relocations
//                  0x0000 Number of Linenumbers
//              0x42000040 Characteristics
//                         CNT_INITIALIZED_DATA
//                         MEM_DISCARDABLE
//                         MEM_READ

// Base Relocation Table
//              0x00004000 Page RVA
//              0x0000000c Block Size
//              0x00000002 Number of Entries
//              Entry 1: Type 0x3 Offset 0x00000196
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00004186 Import Name Table
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
// 0x00002050 [0x000006d8] address [size] of Metadata Directory:        
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
//              0x00000494 Size
//              '#~' Name
//    Stream 2:
//              0x00000500 Offset
//              0x000001b4 Size
//              '#Strings' Name
//    Stream 3:
//              0x000006b4 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x000006b8 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000006c8 Offset
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

// File size            : 9728
// PE header size       : 512 (456 used)    ( 5.26%)
// PE additional info   : 132               ( 1.36%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 0.74%)
// CLR meta-data size  : 1752               (18.01%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 604                ( 6.21%)
// Managed code         : 5987              (61.54%)
// Data                 : 512               ( 5.26%)
// Unaccounted          : 157               ( 1.61%)

// Num.of PE sections   : 2
//   .text    - 8704
//   .reloc   - 512

// CLR meta-data size  : 1752
//   Module        -    1 (10 bytes)
//   TypeDef       -   10 (140 bytes)     0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -   65 (910 bytes)     0 abstract, 0 native, 65 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   433 bytes
//   Blobs         -    16 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   163 bytes

// CLR method headers : 604
//   Num.of method bodies  - 65
//   Num.of fat headers    - 49
//   Num.of tiny headers   - 16

// Managed code : 5987
//   Ave method size - 92
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class T0                             (public) (auto) (ansi) 
// Class T1                             (public) (auto) (ansi) 
// Class T2                             (public) (auto) (ansi) 
// Class T3                             (public) (auto) (ansi) 
// Class T4                             (public) (auto) (ansi) 
// Class T5                             (public) (auto) (ansi) 
// Class T6                             (public) (auto) (ansi) 
// Class T7                             (public) (auto) (ansi) 
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
.module 'text-over-2000.exe'
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
    // Method begins at RVA 0x2728
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
    // Method begins at RVA 0x282c
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
    // Method begins at RVA 0x284c
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

  .method /*06000004*/ public static int32 
          M0_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2874
    // Code size       54 (0x36)
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
    IL_0035:  /* 2A   |                  */ ret
  } // end of method T0::M0_2

  .method /*06000005*/ public static int32 
          M0_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x28ac
    // Code size       72 (0x48)
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
    IL_0047:  /* 2A   |                  */ ret
  } // end of method T0::M0_3

  .method /*06000006*/ public static int32 
          M0_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2900
    // Code size       90 (0x5a)
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
    IL_0059:  /* 2A   |                  */ ret
  } // end of method T0::M0_4

  .method /*06000007*/ public static int32 
          M0_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2968
    // Code size       108 (0x6c)
    .maxstack  9
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
    IL_006b:  /* 2A   |                  */ ret
  } // end of method T0::M0_5

  .method /*06000008*/ public static int32 
          M0_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x29e0
    // Code size       126 (0x7e)
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
    IL_007d:  /* 2A   |                  */ ret
  } // end of method T0::M0_6

  .method /*06000009*/ public static int32 
          M0_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2a6c
    // Code size       144 (0x90)
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
    IL_008f:  /* 2A   |                  */ ret
  } // end of method T0::M0_7

} // end of class T0

.class /*02000004*/ public auto ansi T1
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600000A*/ public static int32 
          M1_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2b08
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

  .method /*0600000B*/ public static int32 
          M1_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2b48
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

  .method /*0600000C*/ public static int32 
          M1_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2ba4
    // Code size       96 (0x60)
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
    IL_005f:  /* 2A   |                  */ ret
  } // end of method T1::M1_2

  .method /*0600000D*/ public static int32 
          M1_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2c10
    // Code size       114 (0x72)
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
    IL_0071:  /* 2A   |                  */ ret
  } // end of method T1::M1_3

  .method /*0600000E*/ public static int32 
          M1_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2c90
    // Code size       132 (0x84)
    .maxstack  9
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
    IL_0083:  /* 2A   |                  */ ret
  } // end of method T1::M1_4

  .method /*0600000F*/ public static int32 
          M1_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2d20
    // Code size       150 (0x96)
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
    IL_0095:  /* 2A   |                  */ ret
  } // end of method T1::M1_5

  .method /*06000010*/ public static int32 
          M1_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2dc4
    // Code size       18 (0x12)
    .maxstack  8
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 2A   |                  */ ret
  } // end of method T1::M1_6

  .method /*06000011*/ public static int32 
          M1_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2dd8
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
  } // end of method T1::M1_7

} // end of class T1

.class /*02000005*/ public auto ansi T2
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000012*/ public static int32 
          M2_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2e00
    // Code size       102 (0x66)
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
    IL_0065:  /* 2A   |                  */ ret
  } // end of method T2::M2_0

  .method /*06000013*/ public static int32 
          M2_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2e74
    // Code size       120 (0x78)
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
    IL_0077:  /* 2A   |                  */ ret
  } // end of method T2::M2_1

  .method /*06000014*/ public static int32 
          M2_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2ef8
    // Code size       138 (0x8a)
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
    IL_0089:  /* 2A   |                  */ ret
  } // end of method T2::M2_2

  .method /*06000015*/ public static int32 
          M2_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x2f90
    // Code size       156 (0x9c)
    .maxstack  9
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
    IL_009b:  /* 2A   |                  */ ret
  } // end of method T2::M2_3

  .method /*06000016*/ public static int32 
          M2_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3038
    // Code size       24 (0x18)
    .maxstack  8
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 2A   |                  */ ret
  } // end of method T2::M2_4

  .method /*06000017*/ public static int32 
          M2_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3054
    // Code size       42 (0x2a)
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
    IL_0029:  /* 2A   |                  */ ret
  } // end of method T2::M2_5

  .method /*06000018*/ public static int32 
          M2_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3080
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
  } // end of method T2::M2_6

  .method /*06000019*/ public static int32 
          M2_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x30c0
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
  } // end of method T2::M2_7

} // end of class T2

.class /*02000006*/ public auto ansi T3
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600001A*/ public static int32 
          M3_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x311c
    // Code size       144 (0x90)
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
    IL_008f:  /* 2A   |                  */ ret
  } // end of method T3::M3_0

  .method /*0600001B*/ public static int32 
          M3_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x31b8
    // Code size       162 (0xa2)
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
    IL_00a1:  /* 2A   |                  */ ret
  } // end of method T3::M3_1

  .method /*0600001C*/ public static int32 
          M3_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3268
    // Code size       30 (0x1e)
    .maxstack  9
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 20   | 05000000         */ ldc.i4     0x5
    IL_001c:  /* 58   |                  */ add
    IL_001d:  /* 2A   |                  */ ret
  } // end of method T3::M3_2

  .method /*0600001D*/ public static int32 
          M3_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3294
    // Code size       48 (0x30)
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
    IL_002f:  /* 2A   |                  */ ret
  } // end of method T3::M3_3

  .method /*0600001E*/ public static int32 
          M3_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x32c8
    // Code size       66 (0x42)
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
    IL_0041:  /* 2A   |                  */ ret
  } // end of method T3::M3_4

  .method /*0600001F*/ public static int32 
          M3_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3318
    // Code size       84 (0x54)
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
    IL_0053:  /* 2A   |                  */ ret
  } // end of method T3::M3_5

  .method /*06000020*/ public static int32 
          M3_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3378
    // Code size       102 (0x66)
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
    IL_0065:  /* 2A   |                  */ ret
  } // end of method T3::M3_6

  .method /*06000021*/ public static int32 
          M3_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x33ec
    // Code size       120 (0x78)
    .maxstack  9
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
    IL_0077:  /* 2A   |                  */ ret
  } // end of method T3::M3_7

} // end of class T3

.class /*02000007*/ public auto ansi T4
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000022*/ public static int32 
          M4_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3470
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
  } // end of method T4::M4_0

  .method /*06000023*/ public static int32 
          M4_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3498
    // Code size       54 (0x36)
    .maxstack  9
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
    IL_0035:  /* 2A   |                  */ ret
  } // end of method T4::M4_1

  .method /*06000024*/ public static int32 
          M4_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x34dc
    // Code size       72 (0x48)
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
    IL_0047:  /* 2A   |                  */ ret
  } // end of method T4::M4_2

  .method /*06000025*/ public static int32 
          M4_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3530
    // Code size       90 (0x5a)
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
    IL_0059:  /* 2A   |                  */ ret
  } // end of method T4::M4_3

  .method /*06000026*/ public static int32 
          M4_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3598
    // Code size       108 (0x6c)
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
    IL_006b:  /* 2A   |                  */ ret
  } // end of method T4::M4_4

  .method /*06000027*/ public static int32 
          M4_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3610
    // Code size       126 (0x7e)
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
    IL_007d:  /* 2A   |                  */ ret
  } // end of method T4::M4_5

  .method /*06000028*/ public static int32 
          M4_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x369c
    // Code size       144 (0x90)
    .maxstack  9
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
    IL_008f:  /* 2A   |                  */ ret
  } // end of method T4::M4_6

  .method /*06000029*/ public static int32 
          M4_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3738
    // Code size       162 (0xa2)
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
    IL_00a1:  /* 2A   |                  */ ret
  } // end of method T4::M4_7

} // end of class T4

.class /*02000008*/ public auto ansi T5
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600002A*/ public static int32 
          M5_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x37e8
    // Code size       78 (0x4e)
    .maxstack  9
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
  } // end of method T5::M5_0

  .method /*0600002B*/ public static int32 
          M5_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3844
    // Code size       96 (0x60)
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
    IL_005f:  /* 2A   |                  */ ret
  } // end of method T5::M5_1

  .method /*0600002C*/ public static int32 
          M5_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x38b0
    // Code size       114 (0x72)
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
    IL_0071:  /* 2A   |                  */ ret
  } // end of method T5::M5_2

  .method /*0600002D*/ public static int32 
          M5_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3930
    // Code size       132 (0x84)
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
    IL_0083:  /* 2A   |                  */ ret
  } // end of method T5::M5_3

  .method /*0600002E*/ public static int32 
          M5_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x39c0
    // Code size       150 (0x96)
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
    IL_0095:  /* 2A   |                  */ ret
  } // end of method T5::M5_4

  .method /*0600002F*/ public static int32 
          M5_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a64
    // Code size       18 (0x12)
    .maxstack  9
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 2A   |                  */ ret
  } // end of method T5::M5_5

  .method /*06000030*/ public static int32 
          M5_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a84
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
  } // end of method T5::M5_6

  .method /*06000031*/ public static int32 
          M5_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3aac
    // Code size       54 (0x36)
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
    IL_0035:  /* 2A   |                  */ ret
  } // end of method T5::M5_7

} // end of class T5

.class /*02000009*/ public auto ansi T6
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000032*/ public static int32 
          M6_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ae4
    // Code size       120 (0x78)
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
    IL_0077:  /* 2A   |                  */ ret
  } // end of method T6::M6_0

  .method /*06000033*/ public static int32 
          M6_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3b68
    // Code size       138 (0x8a)
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
    IL_0089:  /* 2A   |                  */ ret
  } // end of method T6::M6_1

  .method /*06000034*/ public static int32 
          M6_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3c00
    // Code size       156 (0x9c)
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
    IL_009b:  /* 2A   |                  */ ret
  } // end of method T6::M6_2

  .method /*06000035*/ public static int32 
          M6_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ca8
    // Code size       24 (0x18)
    .maxstack  8
    IL_0000:  /* 20   | 01000000         */ ldc.i4     0x1
    IL_0005:  /* 20   | 02000000         */ ldc.i4     0x2
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 20   | 03000000         */ ldc.i4     0x3
    IL_0010:  /* 58   |                  */ add
    IL_0011:  /* 20   | 04000000         */ ldc.i4     0x4
    IL_0016:  /* 58   |                  */ add
    IL_0017:  /* 2A   |                  */ ret
  } // end of method T6::M6_3

  .method /*06000036*/ public static int32 
          M6_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3cc4
    // Code size       42 (0x2a)
    .maxstack  9
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
    IL_0029:  /* 2A   |                  */ ret
  } // end of method T6::M6_4

  .method /*06000037*/ public static int32 
          M6_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3cfc
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
  } // end of method T6::M6_5

  .method /*06000038*/ public static int32 
          M6_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d3c
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
  } // end of method T6::M6_6

  .method /*06000039*/ public static int32 
          M6_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d98
    // Code size       96 (0x60)
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
    IL_005f:  /* 2A   |                  */ ret
  } // end of method T6::M6_7

} // end of class T6

.class /*0200000A*/ public auto ansi T7
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600003A*/ public static int32 
          M7_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3e04
    // Code size       162 (0xa2)
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
    IL_00a1:  /* 2A   |                  */ ret
  } // end of method T7::M7_0

  .method /*0600003B*/ public static int32 
          M7_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3eb4
    // Code size       30 (0x1e)
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
    IL_001d:  /* 2A   |                  */ ret
  } // end of method T7::M7_1

  .method /*0600003C*/ public static int32 
          M7_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ed4
    // Code size       48 (0x30)
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
    IL_002f:  /* 2A   |                  */ ret
  } // end of method T7::M7_2

  .method /*0600003D*/ public static int32 
          M7_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f08
    // Code size       66 (0x42)
    .maxstack  9
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
    IL_0041:  /* 2A   |                  */ ret
  } // end of method T7::M7_3

  .method /*0600003E*/ public static int32 
          M7_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f58
    // Code size       84 (0x54)
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
    IL_0053:  /* 2A   |                  */ ret
  } // end of method T7::M7_4

  .method /*0600003F*/ public static int32 
          M7_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3fb8
    // Code size       102 (0x66)
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
    IL_0065:  /* 2A   |                  */ ret
  } // end of method T7::M7_5

  .method /*06000040*/ public static int32 
          M7_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x402c
    // Code size       120 (0x78)
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
    IL_0077:  /* 2A   |                  */ ret
  } // end of method T7::M7_6

  .method /*06000041*/ public static int32 
          M7_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x40b0
    // Code size       138 (0x8a)
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
    IL_0089:  /* 2A   |                  */ ret
  } // end of method T7::M7_7

} // end of class T7


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
