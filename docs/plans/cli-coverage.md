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
| 0x00 | Module                 | partial | partial | MVID is a content hash; generation and EnC ids fixed     |         |
| 0x01 | TypeRef                | partial | partial | ResolutionScope is the referenced AssemblyRef            |         |
| 0x02 | TypeDef                | partial | partial | Flags from keywords; FieldList hardcoded to 1 (no fields) |         |
| 0x03 | FieldPtr               | partial | n/a     | Count only                                               |         |
| 0x04 | Field                  | none    | none    |                                                          |         |
| 0x05 | MethodPtr              | partial | n/a     | Count only                                               |         |
| 0x06 | MethodDef              | partial | partial | Flags from keywords; ImplFlags 0; ParamList hardcoded to 1; same-module `call` targets (`(call ret (Class) name (params))`, static only; forward calls and recursion) | calls-multi |
| 0x07 | ParamPtr               | partial | n/a     | Count only                                               |         |
| 0x08 | Param                  | none    | none    | Needed for parameter names and `[out]`                   |         |
| 0x09 | InterfaceImpl          | none    | none    | Sorted                                                   |         |
| 0x0A | MemberRef              | partial | partial | Parent is the TypeRef of the call target                 |         |
| 0x0B | Constant               | none    | none    | Sorted                                                   |         |
| 0x0C | CustomAttribute        | none    | none    | Sorted; needs custom attribute blob encoding (II.23.3)   |         |
| 0x0D | FieldMarshal           | none    | none    | Sorted                                                   |         |
| 0x0E | DeclSecurity           | none    | none    | Sorted                                                   |         |
| 0x0F | ClassLayout            | none    | none    | Sorted; needed for explicit and sequential structs       |         |
| 0x10 | FieldLayout            | none    | none    | Sorted                                                   |         |
| 0x11 | StandAloneSig          | partial | partial | Reader parses it; row helper added; LocalVarSig blobs in `sigs.rkt`; `calli` pending | ops-locals-args |
| 0x12 | EventMap               | none    | none    |                                                          |         |
| 0x13 | EventPtr               | partial | n/a     | Count only                                               |         |
| 0x14 | Event                  | none    | none    |                                                          |         |
| 0x15 | PropertyMap            | none    | none    |                                                          |         |
| 0x16 | PropertyPtr            | partial | n/a     | Count only                                               |         |
| 0x17 | Property               | none    | none    |                                                          |         |
| 0x18 | MethodSemantics        | none    | none    | Sorted                                                   |         |
| 0x19 | MethodImpl             | none    | none    | Sorted; explicit interface implementation                |         |
| 0x1A | ModuleRef              | none    | none    | Needed for P/Invoke                                      |         |
| 0x1B | TypeSpec               | partial | partial | Row helper and `read-row`; blob via `sigs.rkt` and reader; generic instance types | generic-calls |
| 0x1C | ImplMap                | none    | none    | Sorted; P/Invoke                                         |         |
| 0x1D | FieldRVA               | none    | none    | Sorted; static data, needs a `.sdata` or `.text` chunk   |         |
| 0x1E | ENCLog                 | partial | n/a     | Count only                                               |         |
| 0x1F | ENCMap                 | partial | n/a     | Count only                                               |         |
| 0x20 | Assembly               | partial | partial | Version, flags, public key, and culture are zero         |         |
| 0x21 | AssemblyProcessor      | partial | n/a     | Count only; should be ignored by readers                 |         |
| 0x22 | AssemblyOS             | partial | n/a     | Count only                                               |         |
| 0x23 | AssemblyRef            | partial | partial | Name comes from `.assembly extern`; version and public key token are zero |  |
| 0x24 | AssemblyRefProcessor   | partial | n/a     | Count only                                               |         |
| 0x25 | AssemblyRefOS          | partial | n/a     | Count only                                               |         |
| 0x26 | File                   | none    | none    | Multi-module assemblies                                  |         |
| 0x27 | ExportedType           | none    | none    | Type forwarders                                          |         |
| 0x28 | ManifestResource       | none    | none    | Embedded resources                                       |         |
| 0x29 | NestedClass            | none    | none    | Sorted                                                   |         |
| 0x2A | GenericParam           | partial | partial | Sorted; written for module generic methods; secondary sort key unverified | generic-calls |
| 0x2B | MethodSpec             | partial | partial | Generic method instantiation; written for `call` with `inst`. Rows match SRM on mscorlib (656) | generic-calls |
| 0x2C | GenericParamConstraint | partial | partial | Sorted; row helper and read                              |         |

## Heaps and streams (II.24)

| Feature                                        | Read    | Write   | Notes                                                 | Fixture |
|------------------------------------------------|---------|---------|-------------------------------------------------------|---------|
| Metadata root, version string                  | partial | partial | Version hardcoded to `v4.0.30319`                     |         |
| `#~` header, `Valid`, `Sorted`, `HeapSizes`    | partial | partial | Writer sets Sorted bits for present sorted tables (for example GenericParam); extra-data flag (0x40, 4 bytes after row counts) not read |         |
| `#-` uncompressed stream                       | none    | n/a     | SRM reads it as a table stream and allows pointer tables. Not in the 6th-edition text; see [verification.md](verification.md#spec-sources-and-discovery) |         |
| Unknown streams (for example `#!` in NGEN images) | none | n/a  | SRM skips them; the reader rejects them             |         |
| `#Strings` (UTF-8, dedup)                      | partial | partial | UTF-8, dedup in insertion order; no suffix sharing    |         |
| `#US` (UTF-16LE, length, trailing flag byte) | partial | partial | Written from `ldstr` literals (`lower.rkt`) | ldstr-hello |
| `#GUID`                                        | partial | partial | MVID content hash (V0)                                |         |
| `#Blob`                                        | partial | partial |                                                       |         |
| 4-byte heap index widths                       | done    | partial | Writer ignores widths in several columns              |         |

## Signatures (II.23.2)

| Feature                                                          | Read | Write   | Fixture |
|------------------------------------------------------------------|------|---------|---------|
| MethodDefSig and MethodRefSig (default, `HASTHIS`, `EXPLICITTHIS`) (II.23.2.1) | partial | partial |         |
| `VARARG` call convention and sentinel                            | none | none    |         |
| Generic method sig (`GENERIC`, `GenParamCount`) (II.23.2.1)      | partial | partial | generic-calls |
| FieldSig (0x06)                                                  | partial | partial | unit tests only (`field-sigs-test.rkt`) |
| PropertySig (0x08)                                               | none | none    |         |
| LocalVarSig (0x07), including `PINNED` and `BYREF` (II.23.2.6)   | partial | partial | ops-locals-args |
| StandAloneMethodSig for `calli`                                  | none | none    |         |
| Primitive element types (`BOOLEAN` through `U`, `STRING`, `OBJECT`) | partial | partial | |
| `CLASS` and `VALUETYPE` with TypeDefOrRefOrSpec encoded tokens   | partial | partial |         |
| `SZARRAY` (`ARRAY` rank, sizes, lower bounds not yet)            | partial | partial | arrays-sum |
| `PTR`, `BYREF` (`FNPTR`, `TYPEDBYREF` not yet)                   | partial | partial |         |
| `GENERICINST`, `VAR`, `MVAR`                                     | partial | partial | generic-calls |
| `CMOD_REQD`, `CMOD_OPT`                                          | none | none    |         |
| TypeSpec and MethodSpec blobs (II.23.2.14, II.23.2.15)           | partial | partial | generic-calls |
| Custom attribute value blobs (II.23.3)                           | none | none    |         |
| Marshalling descriptors (II.23.4)                                | none | none    |         |

## Flags and enumerations (II.23.1)

| Feature                                         | Write status | Fixture |
|-------------------------------------------------|--------------|---------|
| TypeAttributes (visibility, layout, semantics)  | partial (from keywords) |         |
| MethodAttributes and MethodImplAttributes       | partial (from keywords) |         |
| FieldAttributes                                 | constants only (`flags.rkt`), not wired to ilasm | |
| ParamAttributes                                 | constants only (`flags.rkt`), not wired to ilasm | |
| AssemblyFlags and AssemblyHashAlgorithm         | none         |         |
| PInvokeAttributes                               | none         |         |
| GenericParamAttributes                          | none         |         |

Parse ilasm keyword lists (`(public static hidebysig)`) into these flag values instead of writing literals.

## Method bodies and IL (II.25.4, Partition III)

Tracked in [opcodes.md](opcodes.md). Summary: every opcode in the shared table (`src/il/opcodes.rkt`) can be encoded, and the lint decodes all of them. Tiny and fat headers, `.locals` (LocalVarSig), and computed maxstack are done. Catch, finally, fault, and `filter` EH are done, and prefix validation is in. The `il-all-opcodes` fixture is not. The `ops-*` fixtures run arithmetic, branches, constants, conversions, locals and args, and EH.

## Module and type model

| Feature                                                    | Status  | Fixture |
|------------------------------------------------------------|---------|---------|
| Multiple classes with namespaces                           | none    |         |
| `extends` (`System.Object`, `System.ValueType`, `System.Enum`) | none |         |
| Static methods, same-module calls (forward and recursive), parameters | done | calls-multi |
| Instance and static fields, `.ctor`, `.cctor`              | none    |         |
| Instance methods, `newobj`, virtual dispatch, `.override`  | none    |         |
| Interfaces and implementation                              | none    |         |
| Nested types                                               | none    |         |
| Properties and events                                      | none    |         |
| Generic types and methods (generic instances, same-module generic calls) | partial | generic-calls |
| Single-dimension arrays (`newarr`, `ldelem`, `stelem`, `ldlen`; `ldelema` unit-tested only) | done | arrays-sum |
| Value types and enums                                      | none    |         |
| Custom attributes                                          | none    |         |
| P/Invoke                                                   | none    |         |
| Multiple assembly references with versions and public key tokens | none |       |
| Entry point token taken from `.entrypoint`                 | done    | nano    |
| Static data (`.data`, FieldRVA)                            | none    |         |
| Embedded managed resources                                 | none    |         |


## PE image (II.25, PE/COFF)

| Feature                                              | Read    | Write   | Fixture |
|------------------------------------------------------|---------|---------|---------|
| PE32, x86 `ILONLY` EXE                               | done    | partial |         |
| DLL output (`IMAGE_FILE_DLL`, `_CorDllMain`)         | n/a     | none    |         |
| PE32+ (AMD64, ARM64), import stub `movabs`+DIR64    | partial (AMD64 writer via `nano-x64`; ARM64 out of scope) | out of scope |     |
| AnyCPU and `32BITPREFERRED`                          | n/a     | none    |         |
| Subsystem GUI versus console                         | n/a     | none    |         |
| Multiple sections (`.text`, `.rsrc`, `.reloc`, `.sdata`) | partial | partial (`.text`, `.reloc`) |  |
| Sections of any size (no 0x400 limit)                | done    | done    | text-over-400, text-over-2000 |
| Base relocations generated from fixups               | n/a     | partial |         |
| Deterministic timestamp and MVID                     | n/a     | done    | nano    |
| Debug directory and portable PDB                     | out of scope | out of scope |     |
| Win32 resources (version info, manifest)             | none    | none    |         |
| Strong-name signature                                | out of scope | out of scope |     |
| .NET (Core) target with `runtimeconfig.json`         | out of scope | out of scope |     |

## Suggested order

1. Fields, `.ctor`, instance methods, and `newobj` are next. Locals, fat bodies, branching, catch, finally, fault, and filter EH are done. The `ldstr` hello world and `switch` fixtures are done.
3. Multiple types with namespaces, extends, interfaces, nested types.
4. Value types, enums, static data. Single-dimension arrays are done (`arrays-sum`); multi-dimensional arrays are not.
5. Generics: generic methods, TypeSpec, MethodSpec, GenericParam are done. GenericParamConstraint and generic types are not.
6. Properties, events, custom attributes, constants.
7. DLL output and AnyCPU for Framework targets.
8. P/Invoke and Win32 resources. PDB, strong naming, ARM64, and .NET (Core) are out of scope until requested. PE32+ (AMD64) output is covered by `nano-x64`.
