
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
// Addr. of entry point:           0x00002344
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
// 0x000022f8 [0x00000028] address [size] of Import Directory:          
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
//              0x0000034a Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x00000346
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x00002336 Import Name Table
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
// 0x00002050 [0x0000019c] address [size] of Metadata Directory:        
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
//              0x00000064 Size
//              '#Strings' Name
//    Stream 3:
//              0x0000017c Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000180 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000190 Offset
//              0x0000000c Size
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
// CLR meta-data size  : 412                (20.12%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 161                ( 7.86%)
// Managed code         : 107               ( 5.22%)
// Data                 : 512               (25.00%)
// Unaccounted          : 140               ( 6.84%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 412
//   Module        -    1 (10 bytes)
//   TypeDef       -    2 (28 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    3 (18 bytes)
//   MethodDef     -    1 (14 bytes)      0 abstract, 0 native, 1 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -    99 bytes
//   Blobs         -    12 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   163 bytes

// CLR method headers : 161
//   Num.of method bodies  - 1
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 0
//   Num.of fat sections   - 1
//   Num.of small sections - 0

// Managed code : 107
//   Ave method size - 107
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
.module 'ops-eh-finally.exe'
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
    // Method begins at RVA 0x21ec
    // Code size       107 (0x6b)
    .maxstack  8
    .try
    {
      IL_0000:  /* 17   |                  */ ldc.i4.1
      IL_0001:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0006:  /* 18   |                  */ ldc.i4.2
      IL_0007:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_000c:  /* DE   | 07               */ leave.s    IL_0015

    }  // end .try
    finally
    {
      IL_000e:  /* 19   |                  */ ldc.i4.3
      IL_000f:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0014:  /* DC   |                  */ endfinally
    }  // end handler
    // HEX: 02 00 00 00 00 00 00 00 0E 00 00 00 0E 00 00 00 07 00 00 00 00 00 00 00
    .try
    {
      .try
      {
        IL_0015:  /* 1A   |                  */ ldc.i4.4
        IL_0016:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
        IL_001b:  /* 17   |                  */ ldc.i4.1
        IL_001c:  /* 16   |                  */ ldc.i4.0
        IL_001d:  /* 5B   |                  */ div
        IL_001e:  /* 26   |                  */ pop
        IL_001f:  /* DE   | 07               */ leave.s    IL_0028

      }  // end .try
      finally
      {
        IL_0021:  /* 1B   |                  */ ldc.i4.5
        IL_0022:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
        IL_0027:  /* DC   |                  */ endfinally
      }  // end handler
      // HEX: 02 00 00 00 15 00 00 00 0C 00 00 00 21 00 00 00 07 00 00 00 00 00 00 00
      IL_0028:  /* DE   | 09               */ leave.s    IL_0033

    }  // end .try
    catch [mscorlib/*23000001*/]System.Exception/*01000003*/ 
    {
      IL_002a:  /* 26   |                  */ pop
      IL_002b:  /* 1C   |                  */ ldc.i4.6
      IL_002c:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0031:  /* DE   | 00               */ leave.s    IL_0033

    }  // end handler
    // HEX: 00 00 00 00 15 00 00 00 15 00 00 00 2A 00 00 00 09 00 00 00 03 00 00 01
    .try
    {
      IL_0033:  /* 1D   |                  */ ldc.i4.7
      IL_0034:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0039:  /* 1E   |                  */ ldc.i4.8
      IL_003a:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_003f:  /* DE   | 08               */ leave.s    IL_0049

    }  // end .try
    fault
    {
      IL_0041:  /* 1F   | 5A               */ ldc.i4.s   90
      IL_0043:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0048:  /* DC   |                  */ endfinally
    }  // end handler
    // HEX: 04 00 00 00 33 00 00 00 0E 00 00 00 41 00 00 00 08 00 00 00 00 00 00 00
    .try
    {
      .try
      {
        IL_0049:  /* 1F   | 09               */ ldc.i4.s   9
        IL_004b:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
        IL_0050:  /* 17   |                  */ ldc.i4.1
        IL_0051:  /* 16   |                  */ ldc.i4.0
        IL_0052:  /* 5B   |                  */ div
        IL_0053:  /* 26   |                  */ pop
        IL_0054:  /* DE   | 08               */ leave.s    IL_005e

      }  // end .try
      fault
      {
        IL_0056:  /* 1F   | 0A               */ ldc.i4.s   10
        IL_0058:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
        IL_005d:  /* DC   |                  */ endfinally
      }  // end handler
      // HEX: 04 00 00 00 49 00 00 00 0D 00 00 00 56 00 00 00 08 00 00 00 00 00 00 00
      IL_005e:  /* DE   | 0A               */ leave.s    IL_006a

    }  // end .try
    catch [mscorlib/*23000001*/]System.Exception/*01000003*/ 
    {
      IL_0060:  /* 26   |                  */ pop
      IL_0061:  /* 1F   | 0B               */ ldc.i4.s   11
      IL_0063:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
      IL_0068:  /* DE   | 00               */ leave.s    IL_006a

    }  // end handler
    // HEX: 00 00 00 00 49 00 00 00 17 00 00 00 60 00 00 00 0A 00 00 00 03 00 00 01
    IL_006a:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
