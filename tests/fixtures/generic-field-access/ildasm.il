
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
// Addr. of entry point:           0x000023b0
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
// 0x00002364 [0x00000028] address [size] of Import Directory:          
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
//              0x000003b6 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x000003b2
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x000023a2 Import Name Table
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
// 0x00002050 [0x000002a0] address [size] of Metadata Directory:        
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
//              0x00000158 Size
//              '#~' Name
//    Stream 2:
//              0x000001c4 Offset
//              0x00000088 Size
//              '#Strings' Name
//    Stream 3:
//              0x0000024c Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000250 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000260 Offset
//              0x00000040 Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000040908020657 MaskValid
//      0x0000040000000200 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2048
// PE header size       : 512 (456 used)    (25.00%)
// PE additional info   : 132               ( 6.45%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 3.52%)
// CLR meta-data size  : 672                (32.81%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 15                 ( 0.73%)
// Managed code         : 97                ( 4.74%)
// Data                 : 512               (25.00%)
// Unaccounted          : 36                ( 1.76%)

// Num.of PE sections   : 2
//   .text    - 1024
//   .reloc   - 512

// CLR meta-data size  : 672
//   Module        -    1 (10 bytes)
//   TypeDef       -    5 (70 bytes)      1 interfaces, 0 explicit layout
//   TypeRef       -    2 (12 bytes)
//   MethodDef     -    5 (70 bytes)      1 abstract, 0 native, 4 bodies
//   FieldDef      -    1 (6 bytes)       0 constant
//   MemberRef     -    7 (42 bytes)
//   StandAloneSig -    1 (2 bytes)
//   InterfaceImpl -    1 (4 bytes)
//   TypeSpec      -    3 (6 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   GenericParam  -    1 (8 bytes)
//   Strings       -   133 bytes
//   Blobs         -    64 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   183 bytes

// CLR method headers : 15
//   Num.of method bodies  - 4
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 3

// Managed code : 97
//   Ave method size - 24
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Interface IArea                          (public) (abstract) (auto) (ansi) 
// Class Square                         (public) (auto) (ansi) 
// Class Box`1                          (public) (auto) (ansi) 
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
.module 'generic-field-access.exe'
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
    // Method begins at RVA 0x22f0
    // Code size       74 (0x4a)
    .maxstack  8
    .locals /*11000001*/ init (class Box`1/*02000005*/<int32> V_0,
             class Box`1/*02000005*/<class Square/*02000004*/> V_1)
    IL_0000:  /* 1F   | 29               */ ldc.i4.s   41
    IL_0002:  /* 73   | (0A)000001       */ newobj     instance void class Box`1/*02000005*/<int32>/*1B000001*/::.ctor(!0) /* 0A000001 */
    IL_0007:  /* 0A   |                  */ stloc.0
    IL_0008:  /* 06   |                  */ ldloc.0
    IL_0009:  /* 1F   | 2A               */ ldc.i4.s   42
    IL_000b:  /* 7D   | (0A)000002       */ stfld      !0 class Box`1/*02000005*/<int32>/*1B000001*/::Value /* 0A000002 */
    IL_0010:  /* 06   |                  */ ldloc.0
    IL_0011:  /* 7B   | (0A)000002       */ ldfld      !0 class Box`1/*02000005*/<int32>/*1B000001*/::Value /* 0A000002 */
    IL_0016:  /* 28   | (0A)000003       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000003 */
    IL_001b:  /* 06   |                  */ ldloc.0
    IL_001c:  /* 7C   | (0A)000002       */ ldflda     !0 class Box`1/*02000005*/<int32>/*1B000001*/::Value /* 0A000002 */
    IL_0021:  /* 1D   |                  */ ldc.i4.7
    IL_0022:  /* 54   |                  */ stind.i4
    IL_0023:  /* 06   |                  */ ldloc.0
    IL_0024:  /* 7B   | (0A)000002       */ ldfld      !0 class Box`1/*02000005*/<int32>/*1B000001*/::Value /* 0A000002 */
    IL_0029:  /* 28   | (0A)000003       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000003 */
    IL_002e:  /* 73   | (06)000003       */ newobj     instance void Square/*02000004*/::.ctor() /* 06000003 */
    IL_0033:  /* 73   | (0A)000004       */ newobj     instance void class Box`1/*02000005*/<class Square/*02000004*/>/*1B000002*/::.ctor(!0) /* 0A000004 */
    IL_0038:  /* 0B   |                  */ stloc.1
    IL_0039:  /* 07   |                  */ ldloc.1
    IL_003a:  /* 7B   | (0A)000005       */ ldfld      !0 class Box`1/*02000005*/<class Square/*02000004*/>/*1B000002*/::Value /* 0A000005 */
    IL_003f:  /* 6F   | (06)000002       */ callvirt   instance int32 IArea/*02000003*/::Area() /* 06000002 */
    IL_0044:  /* 28   | (0A)000003       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000003 */
    IL_0049:  /* 2A   |                  */ ret
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
    // Method begins at RVA 0x2348
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
    // Method begins at RVA 0x2350
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
    // Method begins at RVA 0x2354
    // Code size       14 (0xe)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000006       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000006 */
    IL_0006:  /* 02   |                  */ ldarg.0
    IL_0007:  /* 03   |                  */ ldarg.1
    IL_0008:  /* 7D   | (0A)000007       */ stfld      !0 class Box`1/*02000005*/<!T>/*1B000003*/::Value /* 0A000007 */
    IL_000d:  /* 2A   |                  */ ret
  } // end of method Box`1::.ctor

} // end of class Box`1


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
