
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
// Addr. of entry point:           0x00002494
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
// 0x00002448 [0x00000028] address [size] of Import Directory:          
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
//              0x0000049a Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x00000496
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00002486 Import Name Table
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
// 0x00002050 [0x000002d8] address [size] of Metadata Directory:        
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
//              0x0000014c Size
//              '#~' Name
//    Stream 2:
//              0x000001b8 Offset
//              0x000000cc Size
//              '#Strings' Name
//    Stream 3:
//              0x00000284 Offset
//              0x0000001c Size
//              '#US' Name
//    Stream 4:
//              0x000002a0 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000002b0 Offset
//              0x00000028 Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000900020457 MaskValid
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
// CLR meta-data size  : 728                (28.44%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 40                 ( 1.56%)
// Managed code         : 232               ( 9.06%)
// Data                 : 512               (20.00%)
// Unaccounted          : 332               (12.97%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 728
//   Module        -    1 (10 bytes)
//   TypeDef       -    4 (56 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    4 (24 bytes)
//   MethodDef     -    7 (98 bytes)      0 abstract, 0 native, 7 bodies
//   FieldDef      -    2 (12 bytes)      0 constant
//   MemberRef     -    4 (24 bytes)
//   StandAloneSig -    2 (4 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   203 bytes
//   Blobs         -    40 bytes
//   UserStrings   -    28 bytes
//   Guids         -    16 bytes
//   Uncategorized -   171 bytes

// CLR method headers : 40
//   Num.of method bodies  - 7
//   Num.of fat headers    - 3
//   Num.of tiny headers   - 4

// Managed code : 232
//   Ave method size - 33
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class Helpers                        (public) (auto) (ansi) 
// Class Store                          (public) (auto) (ansi) 
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
.module 'il-all-opcodes.exe'
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
    // Method begins at RVA 0x2328
    // Code size       21 (0x15)
    .maxstack  8
    IL_0000:  /* 28   | (06)000002       */ call       void Helpers/*02000003*/::BoxOps() /* 06000002 */
    IL_0005:  /* 28   | (06)000003       */ call       void Helpers/*02000003*/::AddressOps() /* 06000003 */
    IL_000a:  /* 28   | (06)000004       */ call       void Helpers/*02000003*/::ConstrainedOps() /* 06000004 */
    IL_000f:  /* 28   | (06)000005       */ call       void Helpers/*02000003*/::FunctionPointers() /* 06000005 */
    IL_0014:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public auto ansi Helpers
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .field /*04000001*/ public static int32 counter
  .method /*06000002*/ public static void 
          BoxOps() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x2340
    // Code size       65 (0x41)
    .maxstack  8
    IL_0000:  /* 1F   | 2A               */ ldc.i4.s   42
    IL_0002:  /* 8C   | (01)000002       */ box        [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0007:  /* A5   | (01)000002       */ unbox.any  [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_000c:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_0011:  /* 1D   |                  */ ldc.i4.7
    IL_0012:  /* 8C   | (01)000002       */ box        [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0017:  /* 79   | (01)000002       */ unbox      [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_001c:  /* 4A   |                  */ ldind.i4
    IL_001d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_0022:  /* 72   | (70)000001       */ ldstr      "cast" /* 70000001 */
    IL_0027:  /* 74   | (01)000004       */ castclass  [mscorlib/*23000001*/]System.String/*01000004*/
    IL_002c:  /* 28   | (0A)000002       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(string) /* 0A000002 */
    IL_0031:  /* 72   | (70)00000B       */ ldstr      "isinst" /* 7000000B */
    IL_0036:  /* 75   | (01)000004       */ isinst     [mscorlib/*23000001*/]System.String/*01000004*/
    IL_003b:  /* 28   | (0A)000002       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(string) /* 0A000002 */
    IL_0040:  /* 2A   |                  */ ret
  } // end of method Helpers::BoxOps

  .method /*06000003*/ public static void 
          AddressOps() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x2390
    // Code size       102 (0x66)
    .maxstack  8
    .locals /*11000001*/ init (int32 V_0,
             int32 V_1)
    IL_0000:  /* FE1C | (01)000002       */ sizeof     [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0006:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_000b:  /* 12   | 00               */ ldloca.s   V_0
    IL_000d:  /* 1B   |                  */ ldc.i4.5
    IL_000e:  /* 81   | (01)000002       */ stobj      [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0013:  /* 12   | 00               */ ldloca.s   V_0
    IL_0015:  /* 71   | (01)000002       */ ldobj      [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_001a:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_001f:  /* 12   | 01               */ ldloca.s   V_1
    IL_0021:  /* 12   | 00               */ ldloca.s   V_0
    IL_0023:  /* 70   | (01)000002       */ cpobj      [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0028:  /* 07   |                  */ ldloc.1
    IL_0029:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_002e:  /* 12   | 01               */ ldloca.s   V_1
    IL_0030:  /* FE15 | (01)000002       */ initobj    [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0036:  /* 07   |                  */ ldloc.1
    IL_0037:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_003c:  /* D0   | (01)000002       */ ldtoken    [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_0041:  /* 26   |                  */ pop
    IL_0042:  /* 19   |                  */ ldc.i4.3
    IL_0043:  /* 73   | (06)000007       */ newobj     instance void Store/*02000004*/::.ctor(int32) /* 06000007 */
    IL_0048:  /* 7C   | (04)000002       */ ldflda     int32 Store/*02000004*/::weight /* 04000002 */
    IL_004d:  /* 4A   |                  */ ldind.i4
    IL_004e:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_0053:  /* 7F   | (04)000001       */ ldsflda    int32 Helpers/*02000003*/::counter /* 04000001 */
    IL_0058:  /* 1F   | 09               */ ldc.i4.s   9
    IL_005a:  /* 54   |                  */ stind.i4
    IL_005b:  /* 7E   | (04)000001       */ ldsfld     int32 Helpers/*02000003*/::counter /* 04000001 */
    IL_0060:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(int32) /* 0A000001 */
    IL_0065:  /* 2A   |                  */ ret
  } // end of method Helpers::AddressOps

  .method /*06000004*/ public static void 
          ConstrainedOps() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x2404
    // Code size       21 (0x15)
    .maxstack  8
    .locals /*11000002*/ init (int32 V_0)
    IL_0000:  /* 1B   |                  */ ldc.i4.5
    IL_0001:  /* 0A   |                  */ stloc.0
    IL_0002:  /* 12   | 00               */ ldloca.s   V_0
    IL_0004:  /* FE16 | (01)000002       */ constrained. [mscorlib/*23000001*/]System.Int32/*01000002*/
    IL_000a:  /* 6F   | (0A)000003       */ callvirt   instance string [mscorlib/*23000001*/]System.Object/*01000001*/::ToString() /* 0A000003 */
    IL_000f:  /* 28   | (0A)000002       */ call       void [mscorlib/*23000001*/]System.Console/*01000003*/::WriteLine(string) /* 0A000002 */
    IL_0014:  /* 2A   |                  */ ret
  } // end of method Helpers::ConstrainedOps

  .method /*06000005*/ public static void 
          FunctionPointers() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x2428
    // Code size       8 (0x8)
    .maxstack  8
    IL_0000:  /* FE06 | (06)000006       */ ldftn      void Helpers/*02000003*/::Target() /* 06000006 */
    IL_0006:  /* 26   |                  */ pop
    IL_0007:  /* 2A   |                  */ ret
  } // end of method Helpers::FunctionPointers

  .method /*06000006*/ public static void 
          Target() cil managed
  // SIG: 00 00 01
  {
    // Method begins at RVA 0x2434
    // Code size       1 (0x1)
    .maxstack  8
    IL_0000:  /* 2A   |                  */ ret
  } // end of method Helpers::Target

} // end of class Helpers

.class /*02000004*/ public auto ansi Store
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .field /*04000002*/ public int32 weight
  .method /*06000007*/ public specialname rtspecialname 
          instance void  .ctor(int32 A_1) cil managed
  // SIG: 20 01 01 08
  {
    // Method begins at RVA 0x2438
    // Code size       14 (0xe)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000004       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000004 */
    IL_0006:  /* 02   |                  */ ldarg.0
    IL_0007:  /* 03   |                  */ ldarg.1
    IL_0008:  /* 7D   | (04)000002       */ stfld      int32 Store/*02000004*/::weight /* 04000002 */
    IL_000d:  /* 2A   |                  */ ret
  } // end of method Store::.ctor

} // end of class Store


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
