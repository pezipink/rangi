
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
// Addr. of entry point:           0x000023fc
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
// 0x000023b0 [0x00000028] address [size] of Import Directory:          
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
//              0x00000402 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x000003fe
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x000023ee Import Name Table
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
// 0x00002050 [0x000002e8] address [size] of Metadata Directory:        
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
//              0x000001a0 Size
//              '#~' Name
//    Stream 2:
//              0x0000020c Offset
//              0x0000008c Size
//              '#Strings' Name
//    Stream 3:
//              0x00000298 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x0000029c Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x000002ac Offset
//              0x0000003c Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000140908020657 MaskValid
//      0x0000140000000200 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2560
// PE header size       : 512 (456 used)    (20.00%)
// PE additional info   : 132               ( 5.16%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 2.81%)
// CLR meta-data size  : 744                (29.06%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 18                 ( 0.70%)
// Managed code         : 98                ( 3.83%)
// Data                 : 512               (20.00%)
// Unaccounted          : 472               (18.44%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 744
//   Module        -    1 (10 bytes)
//   TypeDef       -    6 (84 bytes)      1 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    8 (112 bytes)     1 abstract, 0 native, 7 bodies
//   FieldDef      -    2 (12 bytes)      0 constant
//   MemberRef     -    6 (36 bytes)
//   StandAloneSig -    1 (2 bytes)
//   InterfaceImpl -    1 (4 bytes)
//   TypeSpec      -    2 (4 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   GenericParam  -    2 (16 bytes)
//   GenericParamConstraint-    1 (4 bytes)
//   Strings       -   139 bytes
//   Blobs         -    60 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   187 bytes

// CLR method headers : 18
//   Num.of method bodies  - 7
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 6

// Managed code : 98
//   Ave method size - 14
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Interface IArea                          (public) (abstract) (auto) (ansi) 
// Class Square                         (public) (auto) (ansi) 
// Class Box`1                          (public) (auto) (ansi) 
// Class Holder`1                       (public) (auto) (ansi) 
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
.module 'generic-types.exe'
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
    // Method begins at RVA 0x2338
    // Code size       47 (0x2f)
    .maxstack  8
    .locals /*11000001*/ init (class Box`1/*02000005*/<int32> V_0,
             class Holder`1/*02000006*/<class Square/*02000004*/> V_1)
    IL_0000:  /* 1F   | 29               */ ldc.i4.s   41
    IL_0002:  /* 73   | (0A)000001       */ newobj     instance void class Box`1/*02000005*/<int32>/*1B000001*/::.ctor(!0) /* 0A000001 */
    IL_0007:  /* 0A   |                  */ stloc.0
    IL_0008:  /* 06   |                  */ ldloc.0
    IL_0009:  /* 6F   | (0A)000002       */ callvirt   instance !0 class Box`1/*02000005*/<int32>/*1B000001*/::Get() /* 0A000002 */
    IL_000e:  /* 28   | (0A)000003       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000003 */
    IL_0013:  /* 73   | (06)000003       */ newobj     instance void Square/*02000004*/::.ctor() /* 06000003 */
    IL_0018:  /* 73   | (0A)000004       */ newobj     instance void class Holder`1/*02000006*/<class Square/*02000004*/>/*1B000002*/::.ctor(!0) /* 0A000004 */
    IL_001d:  /* 0B   |                  */ stloc.1
    IL_001e:  /* 07   |                  */ ldloc.1
    IL_001f:  /* 6F   | (0A)000005       */ callvirt   instance !0 class Holder`1/*02000006*/<class Square/*02000004*/>/*1B000002*/::Get() /* 0A000005 */
    IL_0024:  /* 6F   | (06)000002       */ callvirt   instance int32 IArea/*02000003*/::Area() /* 06000002 */
    IL_0029:  /* 28   | (0A)000003       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000003 */
    IL_002e:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ interface public abstract auto ansi IArea
{
  .method /*06000002*/ public newslot abstract virtual 
          instance int32  Area() cil managed
  // SIG: 20 00 08
  {
    // Method begins at RVA 0x0
  } // end of method IArea::Area

} // end of class IArea

.class /*02000004*/ public auto ansi Square
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
       implements IArea/*02000003*/
{
  .method /*06000003*/ public specialname rtspecialname 
          instance void  .ctor() cil managed
  // SIG: 20 00 01
  {
    // Method begins at RVA 0x2374
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000006       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000006 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Square::.ctor

  .method /*06000004*/ public newslot virtual 
          instance int32  Area() cil managed
  // SIG: 20 00 08
  {
    // Method begins at RVA 0x237c
    // Code size       2 (0x2)
    .maxstack  8
    IL_0000:  /* 1A   |                  */ ldc.i4.4
    IL_0001:  /* 2A   |                  */ ret
  } // end of method Square::Area

} // end of class Square

.class /*02000005*/ public auto ansi Box`1<T>
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .field /*04000001*/ public !T Value
  .method /*06000005*/ public specialname rtspecialname 
          instance void  .ctor(!T A_1) cil managed
  // SIG: 20 01 01 13 00
  {
    // Method begins at RVA 0x2380
    // Code size       14 (0xe)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000006       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000006 */
    IL_0006:  /* 02   |                  */ ldarg.0
    IL_0007:  /* 03   |                  */ ldarg.1
    IL_0008:  /* 7D   | (04)000001       */ stfld      !T Box`1/*02000005*/::Value /* 04000001 */
    IL_000d:  /* 2A   |                  */ ret
  } // end of method Box`1::.ctor

  .method /*06000006*/ public instance !T 
          Get() cil managed
  // SIG: 20 00 13 00
  {
    // Method begins at RVA 0x2390
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 7B   | (04)000001       */ ldfld      !T Box`1/*02000005*/::Value /* 04000001 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Box`1::Get

} // end of class Box`1

.class /*02000006*/ public auto ansi Holder`1<class .ctor (IArea/*02000003*/) T>
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .field /*04000002*/ public !T Value
  .method /*06000007*/ public specialname rtspecialname 
          instance void  .ctor(!T A_1) cil managed
  // SIG: 20 01 01 13 00
  {
    // Method begins at RVA 0x2398
    // Code size       14 (0xe)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000006       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000006 */
    IL_0006:  /* 02   |                  */ ldarg.0
    IL_0007:  /* 03   |                  */ ldarg.1
    IL_0008:  /* 7D   | (04)000002       */ stfld      !T Holder`1/*02000006*/::Value /* 04000002 */
    IL_000d:  /* 2A   |                  */ ret
  } // end of method Holder`1::.ctor

  .method /*06000008*/ public instance !T 
          Get() cil managed
  // SIG: 20 00 13 00
  {
    // Method begins at RVA 0x23a8
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 7B   | (04)000002       */ ldfld      !T Holder`1/*02000006*/::Value /* 04000002 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Holder`1::Get

} // end of class Holder`1


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
