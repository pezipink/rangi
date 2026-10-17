
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
// Addr. of entry point:           0x00002328
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
// 0x000022dc [0x00000028] address [size] of Import Directory:          
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
//              0x0000032e Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x0000032a
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000231a Import Name Table
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
// 0x00002050 [0x00000234] address [size] of Metadata Directory:        
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
//              0x0000011c Size
//              '#~' Name
//    Stream 2:
//              0x00000188 Offset
//              0x0000007c Size
//              '#Strings' Name
//    Stream 3:
//              0x00000204 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000208 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000218 Offset
//              0x0000001c Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000902020447 MaskValid
//      0x0000000002000000 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2048
// PE header size       : 512 (456 used)    (25.00%)
// PE additional info   : 132               ( 6.45%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 3.52%)
// CLR meta-data size  : 564                (27.54%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 17                 ( 0.83%)
// Managed code         : 67                ( 3.27%)
// Data                 : 512               (25.00%)
// Unaccounted          : 172               ( 8.40%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 564
//   Module        -    1 (10 bytes)
//   TypeDef       -    4 (56 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    6 (84 bytes)      0 abstract, 0 native, 6 bodies
//   MemberRef     -    2 (12 bytes)
//   MethodImpl    -    1 (6 bytes)
//   StandAloneSig -    1 (2 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   Strings       -   123 bytes
//   Blobs         -    28 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   169 bytes

// CLR method headers : 17
//   Num.of method bodies  - 6
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 5

// Managed code : 67
//   Ave method size - 11
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class Base                           (public) (auto) (ansi) 
// Class Derived                        (public) (auto) (ansi) 
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
.module 'virtual-override.exe'
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
    // Method begins at RVA 0x2284
    // Code size       46 (0x2e)
    .maxstack  8
    .locals /*11000001*/ init (class Base/*02000003*/ V_0,
             class Base/*02000003*/ V_1)
    IL_0000:  /* 73   | (06)000005       */ newobj     instance void Derived/*02000004*/::.ctor() /* 06000005 */
    IL_0005:  /* 0A   |                  */ stloc.0
    IL_0006:  /* 73   | (06)000002       */ newobj     instance void Base/*02000003*/::.ctor() /* 06000002 */
    IL_000b:  /* 0B   |                  */ stloc.1
    IL_000c:  /* 06   |                  */ ldloc.0
    IL_000d:  /* 6F   | (06)000003       */ callvirt   instance int32 Base/*02000003*/::Get() /* 06000003 */
    IL_0012:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0017:  /* 06   |                  */ ldloc.0
    IL_0018:  /* 6F   | (06)000004       */ callvirt   instance int32 Base/*02000003*/::Describe() /* 06000004 */
    IL_001d:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0022:  /* 07   |                  */ ldloc.1
    IL_0023:  /* 6F   | (06)000003       */ callvirt   instance int32 Base/*02000003*/::Get() /* 06000003 */
    IL_0028:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_002d:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public auto ansi Base
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .method /*06000002*/ public specialname rtspecialname 
          instance void  .ctor() cil managed
  // SIG: 20 00 01
  {
    // Method begins at RVA 0x22c0
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000002       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000002 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Base::.ctor

  .method /*06000003*/ public newslot virtual 
          instance int32  Get() cil managed
  // SIG: 20 00 08
  {
    // Method begins at RVA 0x22c8
    // Code size       2 (0x2)
    .maxstack  8
    IL_0000:  /* 17   |                  */ ldc.i4.1
    IL_0001:  /* 2A   |                  */ ret
  } // end of method Base::Get

  .method /*06000004*/ public newslot virtual 
          instance int32  Describe() cil managed
  // SIG: 20 00 08
  {
    // Method begins at RVA 0x22cc
    // Code size       3 (0x3)
    .maxstack  8
    IL_0000:  /* 1F   | 0A               */ ldc.i4.s   10
    IL_0002:  /* 2A   |                  */ ret
  } // end of method Base::Describe

} // end of class Base

.class /*02000004*/ public auto ansi Derived
       extends Base/*02000003*/
{
  .method /*06000005*/ public specialname rtspecialname 
          instance void  .ctor() cil managed
  // SIG: 20 00 01
  {
    // Method begins at RVA 0x22d0
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (06)000002       */ call       instance void Base/*02000003*/::.ctor() /* 06000002 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Derived::.ctor

  .method /*06000006*/ public virtual instance int32 
          Get() cil managed
  // SIG: 20 00 08
  {
    .override Base/*02000003*/::Get /*02000003::06000003*/ 
    // Method begins at RVA 0x22d8
    // Code size       2 (0x2)
    .maxstack  8
    IL_0000:  /* 18   |                  */ ldc.i4.2
    IL_0001:  /* 2A   |                  */ ret
  } // end of method Derived::Get

} // end of class Derived


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
