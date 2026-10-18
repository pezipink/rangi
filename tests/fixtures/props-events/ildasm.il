
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
// Addr. of entry point:           0x000023ac
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
// 0x00002360 [0x00000028] address [size] of Import Directory:          
// 0x00000000 [0x00000000] address [size] of Resource Directory:        
// 0x00000000 [0x00000000] address [size] of Exception Directory:       
// 0x00000000 [0x00000000] address [size] of Security Directory:        
// 0x00004000 [0x0000000c] address [size] of Base Relocation Table:     
// 0x000023b4 [0x00000054] address [size] of Debug Directory:           
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
//              0x00000453 Virtual Size
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
//              Entry 1: Type 0x3 Offset 0x000003ae
//              Entry 2: Type 0x0 Offset 0x00000000

// Import Address Table
//     DLL : mscoree.dll
//              0x00002000 Import Address Table
//              0x0000239e Import Name Table
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
// 0x00002050 [0x000002b4] address [size] of Metadata Directory:        
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
//              0x00000154 Size
//              '#~' Name
//    Stream 2:
//              0x000001c0 Offset
//              0x000000b4 Size
//              '#Strings' Name
//    Stream 3:
//              0x00000274 Offset
//              0x00000004 Size
//              '#US' Name
//    Stream 4:
//              0x00000278 Offset
//              0x00000010 Size
//              '#GUID' Name
//    Stream 5:
//              0x00000288 Offset
//              0x0000002c Size
//              '#Blob' Name

//    Metadata Stream Header:
//              0x00000000 Reserved
//                    0x02 Major
//                    0x00 Minor
//                    0x00 Heaps
//                    0x01 Rid
//      0x0000000901b60457 MaskValid
//      0x0000000001240000 Sorted

// Code Manager Table:
//  default


// Export Address Table Jumps:
// No data.

// File size            : 2560
// PE header size       : 512 (456 used)    (20.00%)
// PE additional info   : 216               ( 8.44%)
// Num.of PE sections   : 2
// CLR header size     : 72                 ( 2.81%)
// CLR meta-data size  : 692                (27.03%)
// CLR additional info : 0                  ( 0.00%)
// CLR method headers  : 17                 ( 0.66%)
// Managed code         : 68                ( 2.66%)
// Data                 : 512               (20.00%)
// Unaccounted          : 471               (18.40%)

// Num.of PE sections   : 2
//   .text    - 1536
//   .reloc   - 512

// CLR meta-data size  : 692
//   Module        -    1 (10 bytes)
//   TypeDef       -    3 (42 bytes)      0 interfaces, 0 explicit layout
//   TypeRef       -    3 (18 bytes)
//   MethodDef     -    6 (84 bytes)      0 abstract, 0 native, 6 bodies
//   FieldDef      -    1 (6 bytes)       0 constant
//   MemberRef     -    2 (12 bytes)
//   StandAloneSig -    1 (2 bytes)
//   PropertyMap   -    1 (4 bytes)
//   Property      -    1 (6 bytes)
//   MethodSemantic-    4 (24 bytes)
//   Assembly      -    1 (22 bytes)
//   AssemblyRef   -    1 (20 bytes)
//   EventMap      -    1 (4 bytes)
//   Event         -    1 (6 bytes)
//   Strings       -   178 bytes
//   Blobs         -    44 bytes
//   UserStrings   -     4 bytes
//   Guids         -    16 bytes
//   Uncategorized -   190 bytes

// CLR method headers : 17
//   Num.of method bodies  - 6
//   Num.of fat headers    - 1
//   Num.of tiny headers   - 5

// Managed code : 68
//   Ave method size - 11
// Classes defined in this module:
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Class Program                        (auto) (ansi) 
// Class Box                            (public) (auto) (ansi) 
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
.module 'props-events.exe'
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
    // Method begins at RVA 0x2304
    // Code size       44 (0x2c)
    .maxstack  8
    .locals /*11000001*/ init (class Box/*02000003*/ V_0)
    IL_0000:  /* 73   | (06)000002       */ newobj     instance void Box/*02000003*/::.ctor() /* 06000002 */
    IL_0005:  /* 0A   |                  */ stloc.0
    IL_0006:  /* 06   |                  */ ldloc.0
    IL_0007:  /* 1F   | 2A               */ ldc.i4.s   42
    IL_0009:  /* 6F   | (06)000004       */ callvirt   instance void Box/*02000003*/::set_Value(int32) /* 06000004 */
    IL_000e:  /* 06   |                  */ ldloc.0
    IL_000f:  /* 6F   | (06)000003       */ callvirt   instance int32 Box/*02000003*/::get_Value() /* 06000003 */
    IL_0014:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_0019:  /* 06   |                  */ ldloc.0
    IL_001a:  /* 1D   |                  */ ldc.i4.7
    IL_001b:  /* 6F   | (06)000004       */ callvirt   instance void Box/*02000003*/::set_Value(int32) /* 06000004 */
    IL_0020:  /* 06   |                  */ ldloc.0
    IL_0021:  /* 6F   | (06)000003       */ callvirt   instance int32 Box/*02000003*/::get_Value() /* 06000003 */
    IL_0026:  /* 28   | (0A)000001       */ call       void [mscorlib/*23000001*/]System.Console/*01000002*/::WriteLine(int32) /* 0A000001 */
    IL_002b:  /* 2A   |                  */ ret
  } // end of method Program::main

} // end of class Program

.class /*02000003*/ public auto ansi Box
       extends [mscorlib/*23000001*/]System.Object/*01000001*/
{
  .field /*04000001*/ private int32 _value
  .method /*06000002*/ public specialname rtspecialname 
          instance void  .ctor() cil managed
  // SIG: 20 00 01
  {
    // Method begins at RVA 0x233c
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 28   | (0A)000002       */ call       instance void [mscorlib/*23000001*/]System.Object/*01000001*/::.ctor() /* 0A000002 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Box::.ctor

  .method /*06000003*/ public specialname 
          instance int32  get_Value() cil managed
  // SIG: 20 00 08
  {
    // Method begins at RVA 0x2344
    // Code size       7 (0x7)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 7B   | (04)000001       */ ldfld      int32 Box/*02000003*/::_value /* 04000001 */
    IL_0006:  /* 2A   |                  */ ret
  } // end of method Box::get_Value

  .method /*06000004*/ public specialname 
          instance void  set_Value(int32 A_1) cil managed
  // SIG: 20 01 01 08
  {
    // Method begins at RVA 0x234c
    // Code size       8 (0x8)
    .maxstack  8
    IL_0000:  /* 02   |                  */ ldarg.0
    IL_0001:  /* 03   |                  */ ldarg.1
    IL_0002:  /* 7D   | (04)000001       */ stfld      int32 Box/*02000003*/::_value /* 04000001 */
    IL_0007:  /* 2A   |                  */ ret
  } // end of method Box::set_Value

  .method /*06000005*/ public specialname 
          instance void  add_Changed(class [mscorlib/*23000001*/]System.EventHandler/*01000003*/ A_1) cil managed
  // SIG: 20 01 01 12 0D
  {
    // Method begins at RVA 0x2358
    // Code size       1 (0x1)
    .maxstack  8
    IL_0000:  /* 2A   |                  */ ret
  } // end of method Box::add_Changed

  .method /*06000006*/ public specialname 
          instance void  remove_Changed(class [mscorlib/*23000001*/]System.EventHandler/*01000003*/ A_1) cil managed
  // SIG: 20 01 01 12 0D
  {
    // Method begins at RVA 0x235c
    // Code size       1 (0x1)
    .maxstack  8
    IL_0000:  /* 2A   |                  */ ret
  } // end of method Box::remove_Changed

  .event /*14000001*/ [mscorlib/*23000001*/]System.EventHandler/*01000003*/ Changed
  {
    .addon instance void Box/*02000003*/::add_Changed(class [mscorlib/*23000001*/]System.EventHandler/*01000003*/) /* 06000005 */
    .removeon instance void Box/*02000003*/::remove_Changed(class [mscorlib/*23000001*/]System.EventHandler/*01000003*/) /* 06000006 */
  } // end of event Box::Changed
  .property /*17000001*/ instance int32 Value()
  {
    .get instance int32 Box/*02000003*/::get_Value() /* 06000003 */
    .set instance void Box/*02000003*/::set_Value(int32) /* 06000004 */
  } // end of property Box::Value
} // end of class Box


// =============================================================

// *********** DISASSEMBLY COMPLETE ***********************
