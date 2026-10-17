
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
// Addr. of entry point:           0x000022e0
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
// 0x00002294 [0x00000028] address [size] of Import Directory:          
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
//              0x000002e6 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x000002e2
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x000022d2 Import Name Table
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
// 0x00002050 [0x00000184] address [size] of Metadata Directory:        
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
//              0x000000a4 Size
//              '#~' Name
//    Stream 2:
//              0x00000110 Offset
//              0x00000054 Size
//              '#Strings' Name
//    Stream 3:
//              0x00000164 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000168 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000178 Offset
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
// CLR meta-data size  : 388                (18.95%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 12                 ( 0.59%)
// Managed code         : 177               ( 8.64%)
// Data                 : 512               (25.00%)
// Unaccounted          : 243               (11.87%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 388
//   Module        -    1 (10 bytes)
//   TypeDef       -    2 (28 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    1 (14 bytes)      0 abstract, 0 native, 1 bodies
//   MemberRef     -    1 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -    84 bytes
//   Blobs         -    12 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   160 bytes

// CLR method headers : 12
//   Num.of method bodies  - 1
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 0

// Managed code : 177
//   Ave method size - 177
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
.module 'ops-arith.exe'
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
    // Method begins at RVA 0x21d4
    // Code size       177 (0xb1)
    .maxstack  8
    IL_0000:  /* 1D   |                  */ ldc.i4.7
    IL_0001:  /* 1B   |                  */ ldc.i4.5
    IL_0002:  /* 58   |                  */ add
    IL_0003:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0008:  /* 1D   |                  */ ldc.i4.7
    IL_0009:  /* 1B   |                  */ ldc.i4.5
    IL_000a:  /* 59   |                  */ sub
    IL_000b:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0010:  /* 1D   |                  */ ldc.i4.7
    IL_0011:  /* 1B   |                  */ ldc.i4.5
    IL_0012:  /* 5A   |                  */ mul
    IL_0013:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0018:  /* 1F   | 11               */ ldc.i4.s   17
    IL_001a:  /* 1B   |                  */ ldc.i4.5
    IL_001b:  /* 5B   |                  */ div
    IL_001c:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0021:  /* 1F   | 11               */ ldc.i4.s   17
    IL_0023:  /* 1B   |                  */ ldc.i4.5
    IL_0024:  /* 5D   |                  */ rem
    IL_0025:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_002a:  /* 1F   | EF               */ ldc.i4.s   -17
    IL_002c:  /* 1B   |                  */ ldc.i4.5
    IL_002d:  /* 5B   |                  */ div
    IL_002e:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0033:  /* 1F   | EF               */ ldc.i4.s   -17
    IL_0035:  /* 1B   |                  */ ldc.i4.5
    IL_0036:  /* 5D   |                  */ rem
    IL_0037:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_003c:  /* 1F   | 09               */ ldc.i4.s   9
    IL_003e:  /* 65   |                  */ neg
    IL_003f:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0044:  /* 1F   | 0C               */ ldc.i4.s   12
    IL_0046:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0048:  /* 5F   |                  */ and
    IL_0049:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_004e:  /* 1F   | 0C               */ ldc.i4.s   12
    IL_0050:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0052:  /* 60   |                  */ or
    IL_0053:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0058:  /* 1F   | 0C               */ ldc.i4.s   12
    IL_005a:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_005c:  /* 61   |                  */ xor
    IL_005d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0062:  /* 16   |                  */ ldc.i4.0
    IL_0063:  /* 66   |                  */ not
    IL_0064:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0069:  /* 19   |                  */ ldc.i4.3
    IL_006a:  /* 1A   |                  */ ldc.i4.4
    IL_006b:  /* 62   |                  */ shl
    IL_006c:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0071:  /* 1F   | F0               */ ldc.i4.s   -16
    IL_0073:  /* 18   |                  */ ldc.i4.2
    IL_0074:  /* 63   |                  */ shr
    IL_0075:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_007a:  /* 1F   | F0               */ ldc.i4.s   -16
    IL_007c:  /* 18   |                  */ ldc.i4.2
    IL_007d:  /* 64   |                  */ shr.un
    IL_007e:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0083:  /* 1B   |                  */ ldc.i4.5
    IL_0084:  /* 1B   |                  */ ldc.i4.5
    IL_0085:  /* FE01 |                  */ ceq
    IL_0087:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_008c:  /* 1B   |                  */ ldc.i4.5
    IL_008d:  /* 1C   |                  */ ldc.i4.6
    IL_008e:  /* FE02 |                  */ cgt
    IL_0090:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0095:  /* 1B   |                  */ ldc.i4.5
    IL_0096:  /* 1C   |                  */ ldc.i4.6
    IL_0097:  /* FE04 |                  */ clt
    IL_0099:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_009e:  /* 15   |                  */ ldc.i4.m1
    IL_009f:  /* 17   |                  */ ldc.i4.1
    IL_00a0:  /* FE03 |                  */ cgt.un
    IL_00a2:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00a7:  /* 15   |                  */ ldc.i4.m1
    IL_00a8:  /* 17   |                  */ ldc.i4.1
    IL_00a9:  /* FE05 |                  */ clt.un
    IL_00ab:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_00b0:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
