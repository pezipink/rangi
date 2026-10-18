
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
// Size of code:                   0x00002400
// Size of init.data:              0x00000200
// Size of uninit.data:            0x00000000
// Addr. of entry point:           0x00004340
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
// 0x000042f4 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00006000 [0x0000000c] address [size] of Base Relocation Table:     
// 0x00004348 [0x00000054] address [size] of Debug Directory:           
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
//              0x000023e7 Virtual Size
//              0x00002000 Virtual Address
//              0x00002400 Size of Raw Data
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
//              0x00002600 Pointer to Raw Data
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
//              Entry 1: Type 0x3 Offset 0x00000342
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00004332 Import Name Table
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
// 0x00002050 [0x0000172c] address [size] of Metadata Directory:        
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
//              0x000004b0 Size
//              '#~' Name
//    Stream 2:
//              0x0000051c Offset
//              0x000001bc Size
//              '#Strings' Name
//    Stream 3:
//              0x000006d8 Offset
//              0x00001034 Size
//              '#US' Name
//    Stream 4:
//              0x0000170c Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x0000171c Offset
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

// File size            : 10240
// PE header size       : 512 (456 used)    ( 5.00%)
// PE additional info   : 216               ( 2.11%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 0.70%)
// CLR meta-data size  : 5932               (57.93%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 297                ( 2.90%)
// Managed code         : 2528              (24.69%)
// Data                 : 512               ( 5.00%)
// Unaccounted          : 171               ( 1.67%)

// Num.of PE sections   : 2
//   .text    - 9216
//   .reloc   - 512

// CLR meta-data size  : 5932
//   Module        -    1 (10 bytes)
//   TypeDef       -   11 (154 bytes)     0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -   66 (924 bytes)     0 abstract, 0 native, 66 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   441 bytes
//   Blobs         -    16 bytes
//   UserStrings   -  4148 bytes
//   Guids         -    16 bytes
//   Uncategorized -   163 bytes

// CLR method headers : 297
//   Num.of method bodies  - 66
//   Num.of fat headers    - 21
//   Num.of tiny headers   - 45

// Managed code : 2528
//   Ave method size - 38
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
// Class T64                            (public) (auto) (ansi) 
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
    // Method begins at RVA 0x377c
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
    // Method begins at RVA 0x3800
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
    // Method begins at RVA 0x3814
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

  .method /*06000004*/ public static int32 
          M0_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3824
    // Code size       19 (0x13)
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
    IL_0012:  /* 2A   |                  */ ret
  } // end of method T0::M0_2

  .method /*06000005*/ public static int32 
          M0_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3838
    // Code size       28 (0x1c)
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
    IL_001b:  /* 2A   |                  */ ret
  } // end of method T0::M0_3

  .method /*06000006*/ public static int32 
          M0_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3858
    // Code size       37 (0x25)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 2A   |                  */ ret
  } // end of method T0::M0_4

  .method /*06000007*/ public static int32 
          M0_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3880
    // Code size       46 (0x2e)
    .maxstack  9
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
    IL_002d:  /* 2A   |                  */ ret
  } // end of method T0::M0_5

  .method /*06000008*/ public static int32 
          M0_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x38bc
    // Code size       55 (0x37)
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
    IL_0036:  /* 2A   |                  */ ret
  } // end of method T0::M0_6

  .method /*06000009*/ public static int32 
          M0_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x38f4
    // Code size       64 (0x40)
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
    IL_003f:  /* 2A   |                  */ ret
  } // end of method T0::M0_7

} // end of class T0

.class /*02000004*/ public auto ansi T1
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600000A*/ public static int32 
          M1_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3940
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

  .method /*0600000B*/ public static int32 
          M1_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3958
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

  .method /*0600000C*/ public static int32 
          M1_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3978
    // Code size       40 (0x28)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 2A   |                  */ ret
  } // end of method T1::M1_2

  .method /*0600000D*/ public static int32 
          M1_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x39a4
    // Code size       49 (0x31)
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
    IL_0030:  /* 2A   |                  */ ret
  } // end of method T1::M1_3

  .method /*0600000E*/ public static int32 
          M1_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x39d8
    // Code size       58 (0x3a)
    .maxstack  9
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
    IL_0039:  /* 2A   |                  */ ret
  } // end of method T1::M1_4

  .method /*0600000F*/ public static int32 
          M1_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a20
    // Code size       67 (0x43)
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
    IL_0042:  /* 2A   |                  */ ret
  } // end of method T1::M1_5

  .method /*06000010*/ public static int32 
          M1_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a70
    // Code size       6 (0x6)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 2A   |                  */ ret
  } // end of method T1::M1_6

  .method /*06000011*/ public static int32 
          M1_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a78
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
  } // end of method T1::M1_7

} // end of class T1

.class /*02000005*/ public auto ansi T2
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000012*/ public static int32 
          M2_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3a88
    // Code size       43 (0x2b)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 1F   | 11               */ ldc.i4.s   17
    IL_0029:  /* 58   |                  */ add
    IL_002a:  /* 2A   |                  */ ret
  } // end of method T2::M2_0

  .method /*06000013*/ public static int32 
          M2_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ab4
    // Code size       52 (0x34)
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
    IL_0033:  /* 2A   |                  */ ret
  } // end of method T2::M2_1

  .method /*06000014*/ public static int32 
          M2_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3aec
    // Code size       61 (0x3d)
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
    IL_003c:  /* 2A   |                  */ ret
  } // end of method T2::M2_2

  .method /*06000015*/ public static int32 
          M2_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3b2c
    // Code size       70 (0x46)
    .maxstack  9
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
    IL_0045:  /* 2A   |                  */ ret
  } // end of method T2::M2_3

  .method /*06000016*/ public static int32 
          M2_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3b80
    // Code size       8 (0x8)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 2A   |                  */ ret
  } // end of method T2::M2_4

  .method /*06000017*/ public static int32 
          M2_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3b8c
    // Code size       14 (0xe)
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
    IL_000d:  /* 2A   |                  */ ret
  } // end of method T2::M2_5

  .method /*06000018*/ public static int32 
          M2_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3b9c
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
  } // end of method T2::M2_6

  .method /*06000019*/ public static int32 
          M2_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3bb4
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
  } // end of method T2::M2_7

} // end of class T2

.class /*02000006*/ public auto ansi T3
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600001A*/ public static int32 
          M3_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3bd4
    // Code size       64 (0x40)
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
    IL_003f:  /* 2A   |                  */ ret
  } // end of method T3::M3_0

  .method /*0600001B*/ public static int32 
          M3_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3c20
    // Code size       73 (0x49)
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
    IL_0048:  /* 2A   |                  */ ret
  } // end of method T3::M3_1

  .method /*0600001C*/ public static int32 
          M3_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3c78
    // Code size       10 (0xa)
    .maxstack  9
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 1B   |                  */ ldc.i4.5
    IL_0008:  /* 58   |                  */ add
    IL_0009:  /* 2A   |                  */ ret
  } // end of method T3::M3_2

  .method /*0600001D*/ public static int32 
          M3_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3c90
    // Code size       16 (0x10)
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
    IL_000f:  /* 2A   |                  */ ret
  } // end of method T3::M3_3

  .method /*0600001E*/ public static int32 
          M3_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ca4
    // Code size       25 (0x19)
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
    IL_0018:  /* 2A   |                  */ ret
  } // end of method T3::M3_4

  .method /*0600001F*/ public static int32 
          M3_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3cc0
    // Code size       34 (0x22)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 2A   |                  */ ret
  } // end of method T3::M3_5

  .method /*06000020*/ public static int32 
          M3_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ce4
    // Code size       43 (0x2b)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 1F   | 11               */ ldc.i4.s   17
    IL_0029:  /* 58   |                  */ add
    IL_002a:  /* 2A   |                  */ ret
  } // end of method T3::M3_6

  .method /*06000021*/ public static int32 
          M3_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d10
    // Code size       52 (0x34)
    .maxstack  9
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
    IL_0033:  /* 2A   |                  */ ret
  } // end of method T3::M3_7

} // end of class T3

.class /*02000007*/ public auto ansi T4
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000022*/ public static int32 
          M4_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d50
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
  } // end of method T4::M4_0

  .method /*06000023*/ public static int32 
          M4_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d60
    // Code size       19 (0x13)
    .maxstack  9
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
    IL_0012:  /* 2A   |                  */ ret
  } // end of method T4::M4_1

  .method /*06000024*/ public static int32 
          M4_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3d80
    // Code size       28 (0x1c)
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
    IL_001b:  /* 2A   |                  */ ret
  } // end of method T4::M4_2

  .method /*06000025*/ public static int32 
          M4_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3da0
    // Code size       37 (0x25)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 2A   |                  */ ret
  } // end of method T4::M4_3

  .method /*06000026*/ public static int32 
          M4_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3dc8
    // Code size       46 (0x2e)
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
    IL_002d:  /* 2A   |                  */ ret
  } // end of method T4::M4_4

  .method /*06000027*/ public static int32 
          M4_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3df8
    // Code size       55 (0x37)
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
    IL_0036:  /* 2A   |                  */ ret
  } // end of method T4::M4_5

  .method /*06000028*/ public static int32 
          M4_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3e30
    // Code size       64 (0x40)
    .maxstack  9
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
    IL_003f:  /* 2A   |                  */ ret
  } // end of method T4::M4_6

  .method /*06000029*/ public static int32 
          M4_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3e7c
    // Code size       73 (0x49)
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
    IL_0048:  /* 2A   |                  */ ret
  } // end of method T4::M4_7

} // end of class T4

.class /*02000008*/ public auto ansi T5
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600002A*/ public static int32 
          M5_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3ed4
    // Code size       31 (0x1f)
    .maxstack  9
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
  } // end of method T5::M5_0

  .method /*0600002B*/ public static int32 
          M5_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f00
    // Code size       40 (0x28)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 2A   |                  */ ret
  } // end of method T5::M5_1

  .method /*0600002C*/ public static int32 
          M5_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f2c
    // Code size       49 (0x31)
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
    IL_0030:  /* 2A   |                  */ ret
  } // end of method T5::M5_2

  .method /*0600002D*/ public static int32 
          M5_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f60
    // Code size       58 (0x3a)
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
    IL_0039:  /* 2A   |                  */ ret
  } // end of method T5::M5_3

  .method /*0600002E*/ public static int32 
          M5_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3f9c
    // Code size       67 (0x43)
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
    IL_0042:  /* 2A   |                  */ ret
  } // end of method T5::M5_4

  .method /*0600002F*/ public static int32 
          M5_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x3fec
    // Code size       6 (0x6)
    .maxstack  9
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 2A   |                  */ ret
  } // end of method T5::M5_5

  .method /*06000030*/ public static int32 
          M5_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4000
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
  } // end of method T5::M5_6

  .method /*06000031*/ public static int32 
          M5_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4010
    // Code size       19 (0x13)
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
    IL_0012:  /* 2A   |                  */ ret
  } // end of method T5::M5_7

} // end of class T5

.class /*02000009*/ public auto ansi T6
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000032*/ public static int32 
          M6_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4024
    // Code size       52 (0x34)
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
    IL_0033:  /* 2A   |                  */ ret
  } // end of method T6::M6_0

  .method /*06000033*/ public static int32 
          M6_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x405c
    // Code size       61 (0x3d)
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
    IL_003c:  /* 2A   |                  */ ret
  } // end of method T6::M6_1

  .method /*06000034*/ public static int32 
          M6_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x409c
    // Code size       70 (0x46)
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
    IL_0045:  /* 2A   |                  */ ret
  } // end of method T6::M6_2

  .method /*06000035*/ public static int32 
          M6_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x40f0
    // Code size       8 (0x8)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 18   |                  */ ldc.i4.2
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 19   |                  */ ldc.i4.3
    IL_0004:  /* 58   |                  */ add
    IL_0005:  /* 1A   |                  */ ldc.i4.4
    IL_0006:  /* 58   |                  */ add
    IL_0007:  /* 2A   |                  */ ret
  } // end of method T6::M6_3

  .method /*06000036*/ public static int32 
          M6_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x40fc
    // Code size       14 (0xe)
    .maxstack  9
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
    IL_000d:  /* 2A   |                  */ ret
  } // end of method T6::M6_4

  .method /*06000037*/ public static int32 
          M6_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4118
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
  } // end of method T6::M6_5

  .method /*06000038*/ public static int32 
          M6_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4130
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
  } // end of method T6::M6_6

  .method /*06000039*/ public static int32 
          M6_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4150
    // Code size       40 (0x28)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 2A   |                  */ ret
  } // end of method T6::M6_7

} // end of class T6

.class /*0200000A*/ public auto ansi T7
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*0600003A*/ public static int32 
          M7_0() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x417c
    // Code size       73 (0x49)
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
    IL_0048:  /* 2A   |                  */ ret
  } // end of method T7::M7_0

  .method /*0600003B*/ public static int32 
          M7_1() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x41d4
    // Code size       10 (0xa)
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
    IL_0009:  /* 2A   |                  */ ret
  } // end of method T7::M7_1

  .method /*0600003C*/ public static int32 
          M7_2() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x41e0
    // Code size       16 (0x10)
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
    IL_000f:  /* 2A   |                  */ ret
  } // end of method T7::M7_2

  .method /*0600003D*/ public static int32 
          M7_3() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x41f4
    // Code size       25 (0x19)
    .maxstack  9
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
    IL_0018:  /* 2A   |                  */ ret
  } // end of method T7::M7_3

  .method /*0600003E*/ public static int32 
          M7_4() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x421c
    // Code size       34 (0x22)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 2A   |                  */ ret
  } // end of method T7::M7_4

  .method /*0600003F*/ public static int32 
          M7_5() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x4240
    // Code size       43 (0x2b)
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
    IL_001e:  /* 1F   | 0E               */ ldc.i4.s   14
    IL_0020:  /* 58   |                  */ add
    IL_0021:  /* 1F   | 0F               */ ldc.i4.s   15
    IL_0023:  /* 58   |                  */ add
    IL_0024:  /* 1F   | 10               */ ldc.i4.s   16
    IL_0026:  /* 58   |                  */ add
    IL_0027:  /* 1F   | 11               */ ldc.i4.s   17
    IL_0029:  /* 58   |                  */ add
    IL_002a:  /* 2A   |                  */ ret
  } // end of method T7::M7_5

  .method /*06000040*/ public static int32 
          M7_6() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x426c
    // Code size       52 (0x34)
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
    IL_0033:  /* 2A   |                  */ ret
  } // end of method T7::M7_6

  .method /*06000041*/ public static int32 
          M7_7() cil managed
  // SIG: 00 00 08
  {
    // Method begins at RVA 0x42a4
    // Code size       61 (0x3d)
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
    IL_003c:  /* 2A   |                  */ ret
  } // end of method T7::M7_7

} // end of class T7

.class /*0200000B*/ public auto ansi T64
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000042*/ public static void 
          Pad() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x42e4
    // Code size       13 (0xd)
    .maxstack  8
    IL_0000:  /* 72   | (70)000001       */ ldstr      "01234567890123456789012345678901234567890123456789"
    + "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890"
    + "12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901"
    + "23456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012"
    + "34567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123"
    + "45678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234"
    + "56789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345"
    + "67890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456"
    + "78901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567"
    + "89012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678"
    + "90123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
    + "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890"
    + "1234567890123456789" /* 70000001 */
    IL_0005:  /* 26   |                  */ pop
    IL_0006:  /* 72   | (70)00093C       */ ldstr      "01234567890123456789012345678901234567890123456789"
    + "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890"
    + "12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901"
    + "23456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012"
    + "34567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123"
    + "45678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234"
    + "56789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345"
    + "67890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456"
    + "78901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567"
    + "89012345678901234567890123456789" /* 7000093C */
    IL_000b:  /* 26   |                  */ pop
    IL_000c:  /* 2A   |                  */ ret
  } // end of method T64::Pad

} // end of class T64


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
