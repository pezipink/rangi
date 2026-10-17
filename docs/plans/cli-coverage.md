---
title: CLI spec coverage tracker
description: Checklist of ECMA-335 and PE/COFF features Rangi reads and writes, with the fixture that proves each one
ms.date: 2026-10-17
---

## How to use this tracker

Status values are `none`, `partial`, and `done`. A feature is `done` only when a fixture under `tests/fixtures/` passes every layer of [verification.md](verification.md). Record the fixture name in the last column. Spec references are ECMA-335 6th edition.

## Metadata tables (II.22)

| Id   | Table                  | Read    | Write   | Notes                                                    | Fixture |
|------|------------------------|---------|---------|----------------------------------------------------------|---------|
| 0x00 | Module                 | partial | partial | MVID constant; generation and EnC ids fixed              |         |
| 0x01 | TypeRef                | partial | partial | ResolutionScope hardcoded to AssemblyRef 1               |         |
| 0x02 | TypeDef                | partial | partial | Flags, Extends, FieldList, and MethodList hardcoded      |         |
| 0x03 | FieldPtr               | none    | n/a     | Uncompressed `#-` streams only                           |         |
| 0x04 | Field                  | none    | none    |                                                          |         |
| 0x05 | MethodPtr              | none    | n/a     |                                                          |         |
| 0x06 | MethodDef              | partial | partial | Flags `0x16` fixed; ImplFlags 0; ParamList 1             |         |
| 0x07 | ParamPtr               | none    | n/a     |                                                          |         |
| 0x08 | Param                  | none    | none    | Needed for parameter names and `[out]`                   |         |
| 0x09 | InterfaceImpl          | none    | none    | Sorted                                                   |         |
| 0x0A | MemberRef              | partial | partial | Parent hardcoded to TypeRef 1                            |         |
| 0x0B | Constant               | none    | none    | Sorted                                                   |         |
| 0x0C | CustomAttribute        | none    | none    | Sorted; needs custom attribute blob encoding (II.23.3)   |         |
| 0x0D | FieldMarshal           | none    | none    | Sorted                                                   |         |
| 0x0E | DeclSecurity           | none    | none    | Sorted                                                   |         |
| 0x0F | ClassLayout            | none    | none    | Sorted; needed for explicit and sequential structs       |         |
| 0x10 | FieldLayout            | none    | none    | Sorted                                                   |         |
| 0x11 | StandAloneSig          | none    | none    | Reader crashes on it; needed for locals and `calli`      |         |
| 0x12 | EventMap               | none    | none    |                                                          |         |
| 0x13 | EventPtr               | none    | n/a     |                                                          |         |
| 0x14 | Event                  | none    | none    |                                                          |         |
| 0x15 | PropertyMap            | none    | none    |                                                          |         |
| 0x16 | PropertyPtr            | none    | n/a     |                                                          |         |
| 0x17 | Property               | none    | none    |                                                          |         |
| 0x18 | MethodSemantics        | none    | none    | Sorted                                                   |         |
| 0x19 | MethodImpl             | none    | none    | Sorted; explicit interface implementation                |         |
| 0x1A | ModuleRef              | none    | none    | Needed for P/Invoke                                      |         |
| 0x1B | TypeSpec               | none    | none    | Needed for generics and arrays                           |         |
| 0x1C | ImplMap                | none    | none    | Sorted; P/Invoke                                         |         |
| 0x1D | FieldRVA               | none    | none    | Sorted; static data, needs a `.sdata` or `.text` chunk   |         |
| 0x1E | ENCLog                 | none    | n/a     |                                                          |         |
| 0x1F | ENCMap                 | none    | n/a     |                                                          |         |
| 0x20 | Assembly               | partial | partial | Version, flags, public key, and culture are zero         |         |
| 0x21 | AssemblyProcessor      | none    | n/a     | Should be ignored by readers                             |         |
| 0x22 | AssemblyOS             | none    | n/a     |                                                          |         |
| 0x23 | AssemblyRef            | partial | partial | Version and public key token are zero; name hardcoded to `mscorlib` |  |
| 0x24 | AssemblyRefProcessor   | none    | n/a     |                                                          |         |
| 0x25 | AssemblyRefOS          | none    | n/a     |                                                          |         |
| 0x26 | File                   | none    | none    | Multi-module assemblies                                  |         |
| 0x27 | ExportedType           | none    | none    | Type forwarders                                          |         |
| 0x28 | ManifestResource       | none    | none    | Embedded resources                                       |         |
| 0x29 | NestedClass            | none    | none    | Sorted                                                   |         |
| 0x2A | GenericParam           | none    | none    | Sorted                                                   |         |
| 0x2B | MethodSpec             | none    | none    | Generic method instantiation                             |         |
| 0x2C | GenericParamConstraint | none    | none    | Sorted                                                   |         |

## Heaps and streams (II.24)

| Feature                                        | Read    | Write   | Notes                                                 | Fixture |
|------------------------------------------------|---------|---------|-------------------------------------------------------|---------|
| Metadata root, version string                  | partial | partial | Version hardcoded to `v4.0.30319`                     |         |
| `#~` header, `Valid`, `Sorted`, `HeapSizes`    | partial | partial | Masks hardcoded on write; extra-data flag ignored     |         |
| `#-` uncompressed stream                       | none    | n/a     |                                                       |         |
| `#Strings` (UTF-8, dedup, suffix sharing)      | partial | partial | Writer uses Latin-1 and no dedup ordering             |         |
| `#US` (UTF-16LE, length, trailing flag byte)   | partial | none    | Writer seeds an unexplained entry; no `ldstr`          |         |
| `#GUID`                                        | partial | partial | Single constant GUID                                  |         |
| `#Blob`                                        | partial | partial |                                                       |         |
| 4-byte heap index widths                       | done    | partial | Writer ignores widths in several columns              |         |

## Signatures (II.23.2)

| Feature                                                          | Read | Write   | Fixture |
|------------------------------------------------------------------|------|---------|---------|
| MethodDefSig and MethodRefSig (default, `HASTHIS`, `EXPLICITTHIS`) | none | partial |         |
| `VARARG` call convention and sentinel                            | none | none    |         |
| Generic method sig (`GENERIC`, `GenParamCount`)                  | none | none    |         |
| FieldSig (0x06)                                                  | none | none    |         |
| PropertySig (0x08)                                               | none | none    |         |
| LocalVarSig (0x07), including `PINNED` and `BYREF`               | none | none    |         |
| StandAloneMethodSig for `calli`                                  | none | none    |         |
| Primitive element types (`BOOLEAN` through `U`, `STRING`, `OBJECT`) | none | partial (`void`, `int32`, `object`) | |
| `CLASS` and `VALUETYPE` with TypeDefOrRefOrSpec encoded tokens   | none | none    |         |
| `SZARRAY`, `ARRAY` (rank, sizes, lower bounds)                   | none | none    |         |
| `PTR`, `BYREF`, `FNPTR`, `TYPEDBYREF`                            | none | none    |         |
| `GENERICINST`, `VAR`, `MVAR`                                     | none | none    |         |
| `CMOD_REQD`, `CMOD_OPT`                                          | none | none    |         |
| TypeSpec and MethodSpec blobs                                    | none | none    |         |
| Custom attribute value blobs (II.23.3)                           | none | none    |         |
| Marshalling descriptors (II.23.4)                                | none | none    |         |

## Flags and enumerations (II.23.1)

| Feature                                         | Write status | Fixture |
|-------------------------------------------------|--------------|---------|
| TypeAttributes (visibility, layout, semantics)  | none (0)     |         |
| MethodAttributes and MethodImplAttributes       | none (fixed) |         |
| FieldAttributes                                 | none         |         |
| ParamAttributes                                 | none         |         |
| AssemblyFlags and AssemblyHashAlgorithm         | none         |         |
| PInvokeAttributes                               | none         |         |
| GenericParamAttributes                          | none         |         |

Parse ilasm keyword lists (`(public static hidebysig)`) into these flag values instead of writing literals.

## Method bodies and IL (II.25.4, Partition III)

Tracked in [opcodes.md](opcodes.md). Summary: 4 of 226 opcodes, tiny headers only, no locals, and no exception handling.

## Module and type model

| Feature                                                    | Status  | Fixture |
|------------------------------------------------------------|---------|---------|
| Multiple classes with namespaces                           | none    |         |
| `extends` (`System.Object`, `System.ValueType`, `System.Enum`) | none |         |
| Instance and static fields, `.ctor`, `.cctor`              | none    |         |
| Instance methods, `newobj`, virtual dispatch, `.override`  | none    |         |
| Interfaces and implementation                              | none    |         |
| Nested types                                               | none    |         |
| Properties and events                                      | none    |         |
| Generic types and methods                                  | none    |         |
| Value types and enums                                      | none    |         |
| Custom attributes                                          | none    |         |
| P/Invoke                                                   | none    |         |
| Multiple assembly references with versions and public key tokens | none |       |
| Entry point token taken from `.entrypoint`                 | none    |         |
| Static data (`.data`, FieldRVA)                            | none    |         |
| Embedded managed resources                                 | none    |         |

## PE image (II.25, PE/COFF)

| Feature                                              | Read    | Write   | Fixture |
|------------------------------------------------------|---------|---------|---------|
| PE32, x86 `ILONLY` EXE                               | done    | partial |         |
| DLL output (`IMAGE_FILE_DLL`, `_CorDllMain`)         | n/a     | none    |         |
| PE32+ (AMD64, ARM64), no import stub needed          | none    | none    |         |
| AnyCPU and `32BITPREFERRED`                          | n/a     | none    |         |
| Subsystem GUI versus console                         | n/a     | none    |         |
| Multiple sections (`.text`, `.rsrc`, `.reloc`, `.sdata`) | partial | partial (`.text`, `.reloc`) |  |
| Sections of any size (no 0x400 limit)                | done    | none    |         |
| Base relocations generated from fixups               | n/a     | partial |         |
| Deterministic timestamp and MVID                     | n/a     | none    |         |
| Debug directory and portable PDB                     | none    | none    |         |
| Win32 resources (version info, manifest)             | none    | none    |         |
| Strong-name signature                                | none    | none    |         |
| .NET (Core) target with `runtimeconfig.json`         | n/a     | none    |         |

## Suggested order

1. Entry point token, flags, multiple TypeRefs and AssemblyRefs, `#US` with `ldstr` (smallest change that makes "hello world" real).
2. Fields, `.ctor`, instance methods, `newobj`, locals and fat bodies, then branching and EH.
3. Multiple types with namespaces, extends, interfaces, nested types.
4. Value types, enums, arrays, static data.
5. Generics (TypeSpec, MethodSpec, GenericParam, GenericParamConstraint).
6. Properties, events, custom attributes, constants.
7. DLL output, PE32+, AnyCPU, .NET (Core) target.
8. P/Invoke, resources, PDB, strong naming.
