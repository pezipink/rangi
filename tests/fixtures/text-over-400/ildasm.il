
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
// Addr. of entry point:           0x00002378
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
// 0x0000232c [0x00000028] address [size] of Import Directory:          
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
//              0x0000037e Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x0000037a
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000236a Import Name Table
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

// File size            : 2048
// PE header size       : 512 (456 used)    (25.00%)
// PE additional info   : 132               ( 6.45%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 3.52%)
// CLR meta-data size  : 508                (24.80%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 27                 ( 1.32%)
// Managed code         : 188               ( 9.18%)
// Data                 : 512               (25.00%)
// Unaccounted          : 97                ( 4.74%)

// Num.of PE sections   : 2
//   .text    - 1024
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

// CLR method headers : 27
//   Num.of method bodies  - 5
//   Num.of fat headers    - 2
//   Num.of tiny headers   - 3

// Managed code : 188
//   Ave method size - 37
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
    // Code size       117 (0x75)
    .maxstack  2
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 1B   |                  */ ldc.i4.5
    IL_0008:  /* 58   |                  */ add
    IL_0009:  /* 1C   |                  */ ldc.i4.6
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 1D   |                  */ ldc.i4.7
    IL_000c:  /* 58   |                  */ add
    IL_000d:  /* 1E   |                  */ ldc.i4.8
    IL_000e:  /* 58   |                  */ add
    IL_000f:  /* 1F   | 09               */ ldc.i4.s   9
    IL_0011:  /* 58   |                  */ add
    IL_0012:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0014:  /* 58   |                  */ add
    IL_0015:  /* 1F   | 0B               */ ldc.i4.s   11
    IL_0017:  /* 58   |                  */ add
    IL_0018:  /* 1F   | 0C               */ ldc.i4.s   12
    IL_001a:  /* 58   |                  */ add
    IL_001b:  /* 1F   | 0D               */ ldc.i4.s   13
    IL_001d:  /* 58   |                  */ add
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 1F   | 11               */ ldc.i4.s   17
    IL_0029:  /* 58   |                  */ add
    IL_002a:  /* 1F   | 12               */ ldc.i4.s   18
    IL_002c:  /* 58   |                  */ add
    IL_002d:  /* 1F   | 13               */ ldc.i4.s   19
    IL_002f:  /* 58   |                  */ add
    IL_0030:  /* 1F   | 14               */ ldc.i4.s   20
    IL_0032:  /* 58   |                  */ add
    IL_0033:  /* 1F   | 15               */ ldc.i4.s   21
    IL_0035:  /* 58   |                  */ add
    IL_0036:  /* 1F   | 16               */ ldc.i4.s   22
    IL_0038:  /* 58   |                  */ add
    IL_0039:  /* 1F   | 17               */ ldc.i4.s   23
    IL_003b:  /* 58   |                  */ add
    IL_003c:  /* 1F   | 18               */ ldc.i4.s   24
    IL_003e:  /* 58   |                  */ add
    IL_003f:  /* 1F   | 19               */ ldc.i4.s   25
    IL_0041:  /* 58   |                  */ add
    IL_0042:  /* 1F   | 1A               */ ldc.i4.s   26
    IL_0044:  /* 58   |                  */ add
    IL_0045:  /* 1F   | 1B               */ ldc.i4.s   27
    IL_0047:  /* 58   |                  */ add
    IL_0048:  /* 1F   | 1C               */ ldc.i4.s   28
    IL_004a:  /* 58   |                  */ add
    IL_004b:  /* 1F   | 1D               */ ldc.i4.s   29
    IL_004d:  /* 58   |                  */ add
    IL_004e:  /* 1F   | 1E               */ ldc.i4.s   30
    IL_0050:  /* 58   |                  */ add
    IL_0051:  /* 1F   | 1F               */ ldc.i4.s   31
    IL_0053:  /* 58   |                  */ add
    IL_0054:  /* 1F   | 20               */ ldc.i4.s   32
    IL_0056:  /* 58   |                  */ add
    IL_0057:  /* 1F   | 21               */ ldc.i4.s   33
    IL_0059:  /* 58   |                  */ add
    IL_005a:  /* 1F   | 22               */ ldc.i4.s   34
    IL_005c:  /* 58   |                  */ add
    IL_005d:  /* 1F   | 23               */ ldc.i4.s   35
    IL_005f:  /* 58   |                  */ add
    IL_0060:  /* 1F   | 24               */ ldc.i4.s   36
    IL_0062:  /* 58   |                  */ add
    IL_0063:  /* 1F   | 25               */ ldc.i4.s   37
    IL_0065:  /* 58   |                  */ add
    IL_0066:  /* 1F   | 26               */ ldc.i4.s   38
    IL_0068:  /* 58   |                  */ add
    IL_0069:  /* 1F   | 27               */ ldc.i4.s   39
    IL_006b:  /* 58   |                  */ add
    IL_006c:  /* 1F   | 28               */ ldc.i4.s   40
    IL_006e:  /* 58   |                  */ add
    IL_006f:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0074:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public auto ansi T0
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000002*/ public static int32 
          M0_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x22d0
    // Code size       6 (0x6)
    .maxstack  9
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 2A   |                  */ ret
  } // end of method T0::M0_0

  .method /*06000003*/ public static int32 
          M0_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x22e4
    // Code size       12 (0xc)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 1B   |                  */ ldc.i4.5
    IL_0008:  /* 58   |                  */ add
    IL_0009:  /* 1C   |                  */ ldc.i4.6
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 2A   |                  */ ret
  } // end of method T0::M0_1

} // end of class T0

.class /*02000004*/ public auto ansi T1
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000004*/ public static int32 
          M1_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x22f4
    // Code size       22 (0x16)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 1B   |                  */ ldc.i4.5
    IL_0008:  /* 58   |                  */ add
    IL_0009:  /* 1C   |                  */ ldc.i4.6
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 1D   |                  */ ldc.i4.7
    IL_000c:  /* 58   |                  */ add
    IL_000d:  /* 1E   |                  */ ldc.i4.8
    IL_000e:  /* 58   |                  */ add
    IL_000f:  /* 1F   | 09               */ ldc.i4.s   9
    IL_0011:  /* 58   |                  */ add
    IL_0012:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0014:  /* 58   |                  */ add
    IL_0015:  /* 2A   |                  */ ret
  } // end of method T1::M1_0

  .method /*06000005*/ public static int32 
          M1_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x230c
    // Code size       31 (0x1f)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 1B   |                  */ ldc.i4.5
    IL_0008:  /* 58   |                  */ add
    IL_0009:  /* 1C   |                  */ ldc.i4.6
    IL_000a:  /* 58   |                  */ add
    IL_000b:  /* 1D   |                  */ ldc.i4.7
    IL_000c:  /* 58   |                  */ add
    IL_000d:  /* 1E   |                  */ ldc.i4.8
    IL_000e:  /* 58   |                  */ add
    IL_000f:  /* 1F   | 09               */ ldc.i4.s   9
    IL_0011:  /* 58   |                  */ add
    IL_0012:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0014:  /* 58   |                  */ add
    IL_0015:  /* 1F   | 0B               */ ldc.i4.s   11
    IL_0017:  /* 58   |                  */ add
    IL_0018:  /* 1F   | 0C               */ ldc.i4.s   12
    IL_001a:  /* 58   |                  */ add
    IL_001b:  /* 1F   | 0D               */ ldc.i4.s   13
    IL_001d:  /* 58   |                  */ add
    IL_001e:  /* 2A   |                  */ ret
  } // end of method T1::M1_1

} // end of class T1


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
