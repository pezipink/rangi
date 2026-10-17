
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
// Addr. of entry point:           0x0000255c
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
// 0x00002510 [0x00000028] address [size] of Import Directory:          
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
//              0x00000562 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x0000055e
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000254e Import Name Table
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
// 0x00002050 [0x00000194] address [size] of Metadata Directory:        
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
//              0x000000ac Size
//              '#~' Name
//    Stream 2:
//              0x00000118 Offset
//              0x00000058 Size
//              '#Strings' Name
//    Stream 3:
//              0x00000170 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000174 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000184 Offset
//              0x00000010 Size
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

// File size            : 2560
// PE header size       : 512 (456 used)    (20.00%)
// PE additional info   : 132               ( 5.16%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 2.81%)
// CLR meta-data size  : 404                (15.78%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 12                 ( 0.47%)
// Managed code         : 797               (31.13%)
// Data                 : 512               (20.00%)
// Unaccounted          : 119               ( 4.65%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 404
//   Module        -    1 (10 bytes)
//   TypeDef       -    2 (28 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    1 (14 bytes)      0 abstract, 0 native, 1 bodies
//   MemberRef     -    1 (6 bytes)
//   StandAloneSig -    1 (2 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -    85 bytes
//   Blobs         -    16 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   169 bytes

// CLR method headers : 12
//   Num.of method bodies  - 1
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 0

// Managed code : 797
//   Ave method size - 797
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
.module 'ops-branch.exe'
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
    // Method begins at RVA 0x21e4
    // Code size       797 (0x31d)
    .maxstack  8
    .locals /*11000001*/ init (int32 V_0)
    IL_0000:  /* 16   |                  */ ldc.i4.0
    IL_0001:  /* 0A   |                  */ stloc.0
    IL_0002:  /* 06   |                  */ ldloc.0
    IL_0003:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0008:  /* 06   |                  */ ldloc.0
    IL_0009:  /* 17   |                  */ ldc.i4.1
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 0A   |                  */ stloc.0
    IL_000c:  /* 06   |                  */ ldloc.0
    IL_000d:  /* 1B   |                  */ ldc.i4.5
    IL_000e:  /* 32   | F2               */ blt.s      IL_0002

    IL_0010:  /* 19   |                  */ ldc.i4.3
    IL_0011:  /* 19   |                  */ ldc.i4.3
    IL_0012:  /* 2E   | 08               */ beq.s      IL_001c

    IL_0014:  /* 16   |                  */ ldc.i4.0
    IL_0015:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_001a:  /* 2B   | 06               */ br.s       IL_0022

    IL_001c:  /* 17   |                  */ ldc.i4.1
    IL_001d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0022:  /* 19   |                  */ ldc.i4.3
    IL_0023:  /* 1A   |                  */ ldc.i4.4
    IL_0024:  /* 33   | 08               */ bne.un.s   IL_002e

    IL_0026:  /* 16   |                  */ ldc.i4.0
    IL_0027:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_002c:  /* 2B   | 06               */ br.s       IL_0034

    IL_002e:  /* 17   |                  */ ldc.i4.1
    IL_002f:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0034:  /* 15   |                  */ ldc.i4.m1
    IL_0035:  /* 17   |                  */ ldc.i4.1
    IL_0036:  /* 32   | 08               */ blt.s      IL_0040

    IL_0038:  /* 16   |                  */ ldc.i4.0
    IL_0039:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_003e:  /* 2B   | 06               */ br.s       IL_0046

    IL_0040:  /* 17   |                  */ ldc.i4.1
    IL_0041:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0046:  /* 1B   |                  */ ldc.i4.5
    IL_0047:  /* 18   |                  */ ldc.i4.2
    IL_0048:  /* 30   | 08               */ bgt.s      IL_0052

    IL_004a:  /* 16   |                  */ ldc.i4.0
    IL_004b:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0050:  /* 2B   | 06               */ br.s       IL_0058

    IL_0052:  /* 17   |                  */ ldc.i4.1
    IL_0053:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0058:  /* 18   |                  */ ldc.i4.2
    IL_0059:  /* 18   |                  */ ldc.i4.2
    IL_005a:  /* 31   | 08               */ ble.s      IL_0064

    IL_005c:  /* 16   |                  */ ldc.i4.0
    IL_005d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0062:  /* 2B   | 06               */ br.s       IL_006a

    IL_0064:  /* 17   |                  */ ldc.i4.1
    IL_0065:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_006a:  /* 17   |                  */ ldc.i4.1
    IL_006b:  /* 18   |                  */ ldc.i4.2
    IL_006c:  /* 2F   | 08               */ bge.s      IL_0076

    IL_006e:  /* 16   |                  */ ldc.i4.0
    IL_006f:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0074:  /* 2B   | 06               */ br.s       IL_007c

    IL_0076:  /* 17   |                  */ ldc.i4.1
    IL_0077:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_007c:  /* 1D   |                  */ ldc.i4.7
    IL_007d:  /* 2D   | 08               */ brtrue.s   IL_0087

    IL_007f:  /* 16   |                  */ ldc.i4.0
    IL_0080:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0085:  /* 2B   | 06               */ br.s       IL_008d

    IL_0087:  /* 17   |                  */ ldc.i4.1
    IL_0088:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_008d:  /* 16   |                  */ ldc.i4.0
    IL_008e:  /* 2C   | 08               */ brfalse.s  IL_0098

    IL_0090:  /* 16   |                  */ ldc.i4.0
    IL_0091:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0096:  /* 2B   | 06               */ br.s       IL_009e

    IL_0098:  /* 17   |                  */ ldc.i4.1
    IL_0099:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_009e:  /* 16   |                  */ ldc.i4.0
    IL_009f:  /* 2D   | 08               */ brtrue.s   IL_00a9

    IL_00a1:  /* 16   |                  */ ldc.i4.0
    IL_00a2:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00a7:  /* 2B   | 06               */ br.s       IL_00af

    IL_00a9:  /* 17   |                  */ ldc.i4.1
    IL_00aa:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00af:  /* 17   |                  */ ldc.i4.1
    IL_00b0:  /* 17   |                  */ ldc.i4.1
    IL_00b1:  /* 3B   | 5F020000         */ beq        IL_0315

    IL_00b6:  /* 1F   | 63               */ ldc.i4.s   99
    IL_00b8:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00bd:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00c2:  /* 26   |                  */ pop
    IL_00c3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00c8:  /* 26   |                  */ pop
    IL_00c9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00ce:  /* 26   |                  */ pop
    IL_00cf:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00d4:  /* 26   |                  */ pop
    IL_00d5:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00da:  /* 26   |                  */ pop
    IL_00db:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00e0:  /* 26   |                  */ pop
    IL_00e1:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00e6:  /* 26   |                  */ pop
    IL_00e7:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00ec:  /* 26   |                  */ pop
    IL_00ed:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00f2:  /* 26   |                  */ pop
    IL_00f3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00f8:  /* 26   |                  */ pop
    IL_00f9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_00fe:  /* 26   |                  */ pop
    IL_00ff:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0104:  /* 26   |                  */ pop
    IL_0105:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_010a:  /* 26   |                  */ pop
    IL_010b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0110:  /* 26   |                  */ pop
    IL_0111:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0116:  /* 26   |                  */ pop
    IL_0117:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_011c:  /* 26   |                  */ pop
    IL_011d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0122:  /* 26   |                  */ pop
    IL_0123:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0128:  /* 26   |                  */ pop
    IL_0129:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_012e:  /* 26   |                  */ pop
    IL_012f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0134:  /* 26   |                  */ pop
    IL_0135:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_013a:  /* 26   |                  */ pop
    IL_013b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0140:  /* 26   |                  */ pop
    IL_0141:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0146:  /* 26   |                  */ pop
    IL_0147:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_014c:  /* 26   |                  */ pop
    IL_014d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0152:  /* 26   |                  */ pop
    IL_0153:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0158:  /* 26   |                  */ pop
    IL_0159:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_015e:  /* 26   |                  */ pop
    IL_015f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0164:  /* 26   |                  */ pop
    IL_0165:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_016a:  /* 26   |                  */ pop
    IL_016b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0170:  /* 26   |                  */ pop
    IL_0171:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0176:  /* 26   |                  */ pop
    IL_0177:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_017c:  /* 26   |                  */ pop
    IL_017d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0182:  /* 26   |                  */ pop
    IL_0183:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0188:  /* 26   |                  */ pop
    IL_0189:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_018e:  /* 26   |                  */ pop
    IL_018f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0194:  /* 26   |                  */ pop
    IL_0195:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_019a:  /* 26   |                  */ pop
    IL_019b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01a0:  /* 26   |                  */ pop
    IL_01a1:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01a6:  /* 26   |                  */ pop
    IL_01a7:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01ac:  /* 26   |                  */ pop
    IL_01ad:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01b2:  /* 26   |                  */ pop
    IL_01b3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01b8:  /* 26   |                  */ pop
    IL_01b9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01be:  /* 26   |                  */ pop
    IL_01bf:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01c4:  /* 26   |                  */ pop
    IL_01c5:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01ca:  /* 26   |                  */ pop
    IL_01cb:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01d0:  /* 26   |                  */ pop
    IL_01d1:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01d6:  /* 26   |                  */ pop
    IL_01d7:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01dc:  /* 26   |                  */ pop
    IL_01dd:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01e2:  /* 26   |                  */ pop
    IL_01e3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01e8:  /* 26   |                  */ pop
    IL_01e9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01ee:  /* 26   |                  */ pop
    IL_01ef:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01f4:  /* 26   |                  */ pop
    IL_01f5:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_01fa:  /* 26   |                  */ pop
    IL_01fb:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0200:  /* 26   |                  */ pop
    IL_0201:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0206:  /* 26   |                  */ pop
    IL_0207:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_020c:  /* 26   |                  */ pop
    IL_020d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0212:  /* 26   |                  */ pop
    IL_0213:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0218:  /* 26   |                  */ pop
    IL_0219:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_021e:  /* 26   |                  */ pop
    IL_021f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0224:  /* 26   |                  */ pop
    IL_0225:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_022a:  /* 26   |                  */ pop
    IL_022b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0230:  /* 26   |                  */ pop
    IL_0231:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0236:  /* 26   |                  */ pop
    IL_0237:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_023c:  /* 26   |                  */ pop
    IL_023d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0242:  /* 26   |                  */ pop
    IL_0243:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0248:  /* 26   |                  */ pop
    IL_0249:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_024e:  /* 26   |                  */ pop
    IL_024f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0254:  /* 26   |                  */ pop
    IL_0255:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_025a:  /* 26   |                  */ pop
    IL_025b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0260:  /* 26   |                  */ pop
    IL_0261:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0266:  /* 26   |                  */ pop
    IL_0267:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_026c:  /* 26   |                  */ pop
    IL_026d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0272:  /* 26   |                  */ pop
    IL_0273:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0278:  /* 26   |                  */ pop
    IL_0279:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_027e:  /* 26   |                  */ pop
    IL_027f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0284:  /* 26   |                  */ pop
    IL_0285:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_028a:  /* 26   |                  */ pop
    IL_028b:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0290:  /* 26   |                  */ pop
    IL_0291:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0296:  /* 26   |                  */ pop
    IL_0297:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_029c:  /* 26   |                  */ pop
    IL_029d:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02a2:  /* 26   |                  */ pop
    IL_02a3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02a8:  /* 26   |                  */ pop
    IL_02a9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02ae:  /* 26   |                  */ pop
    IL_02af:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02b4:  /* 26   |                  */ pop
    IL_02b5:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02ba:  /* 26   |                  */ pop
    IL_02bb:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02c0:  /* 26   |                  */ pop
    IL_02c1:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02c6:  /* 26   |                  */ pop
    IL_02c7:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02cc:  /* 26   |                  */ pop
    IL_02cd:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02d2:  /* 26   |                  */ pop
    IL_02d3:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02d8:  /* 26   |                  */ pop
    IL_02d9:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02de:  /* 26   |                  */ pop
    IL_02df:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02e4:  /* 26   |                  */ pop
    IL_02e5:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02ea:  /* 26   |                  */ pop
    IL_02eb:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02f0:  /* 26   |                  */ pop
    IL_02f1:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02f6:  /* 26   |                  */ pop
    IL_02f7:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_02fc:  /* 26   |                  */ pop
    IL_02fd:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0302:  /* 26   |                  */ pop
    IL_0303:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0308:  /* 26   |                  */ pop
    IL_0309:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_030e:  /* 26   |                  */ pop
    IL_030f:  /* 20   | 40420F00         */ ldc.i4     0xf4240
    IL_0314:  /* 26   |                  */ pop
    IL_0315:  /* 1F   | 2A               */ ldc.i4.s   42
    IL_0317:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_031c:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
