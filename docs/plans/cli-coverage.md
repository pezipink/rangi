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
| 0x02 | TypeDef                | partial | partial | Flags from keywords; FieldList from each class's field run |         |
| 0x03 | FieldPtr               | partial | n/a     | Count only                                               |         |
| 0x04 | Field                  | partial | partial | Same-module fields from `.field` keywords and FieldSig; `ldsfld`/`stsfld` checked for static-ness and type. Instance fields have no positive fixture yet | static-fields |
| 0x05 | MethodPtr              | partial | n/a     | Count only                                               |         |
| 0x06 | MethodDef              | partial | partial | Flags from keywords; ImplFlags 0; ParamList hardcoded to 1; same-module `call` targets (`(call ret (Class) name (params))`, static only; forward calls and recursion) | calls-multi |
| 0x07 | ParamPtr               | partial | n/a     | Count only                                               |         |
| 0x08 | Param                  | none    | none    | Needed for parameter names and `[out]`                   |         |
| 0x09 | InterfaceImpl          | partial | partial | Sorted; `.implements` rows (same-module and external interfaces); no interface inheritance | interfaces |
| 0x0A | MemberRef              | partial | partial | Parent is the TypeRef of the call target                 |         |
| 0x0B | Constant               | none    | none    | Sorted                                                   |         |
| 0x0C | CustomAttribute        | partial | partial | Sorted by Parent; `.custom` on assembly, class, and method parents; Module parent not supported. Value blobs are literal bytes (II.23.3 prolog checked), not typed | custom-attrs |
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
| 0x19 | MethodImpl             | partial | partial | Sorted; `.override` rows (same-module and external base); interface implementation not | virtual-override |
| 0x1A | ModuleRef              | partial | done    | One row per P/Invoke DLL, first-use order (II.22.31)     | pinvoke |
| 0x1B | TypeSpec               | partial | partial | Row helper and `read-row`; blob via `sigs.rkt` and reader; generic instance types | generic-calls |
| 0x1C | ImplMap                | partial | done    | Sorted by MemberForwarded; P/Invoke (II.22.22)           | pinvoke |
| 0x1D | FieldRVA               | none    | done    | Sorted; RVA of the static field's `.data` chunk in `.sdata` (II.22.18) | static-data |
| 0x1E | ENCLog                 | partial | n/a     | Count only                                               |         |
| 0x1F | ENCMap                 | partial | n/a     | Count only                                               |         |
| 0x20 | Assembly               | partial | partial | Version, flags, public key, and culture are zero         |         |
| 0x21 | AssemblyProcessor      | partial | n/a     | Count only; should be ignored by readers                 |         |
| 0x22 | AssemblyOS             | partial | n/a     | Count only                                               |         |
| 0x23 | AssemblyRef            | partial | partial | Name, version, and public key token come from `.assembly extern` (II.22.5); Flags and HashValue are zero, and full public keys are not written | asm-refs-versioned |
| 0x24 | AssemblyRefProcessor   | partial | n/a     | Count only                                               |         |
| 0x25 | AssemblyRefOS          | partial | n/a     | Count only                                               |         |
| 0x26 | File                   | none    | none    | Multi-module assemblies                                  |         |
| 0x27 | ExportedType           | none    | none    | Type forwarders                                          |         |
| 0x28 | ManifestResource       | none    | none    | Embedded resources                                       |         |
| 0x29 | NestedClass            | partial | done    | Sorted by NestedClass; one row per nested type, from textual nested `.class`; read back via `read-row` only | nested-types |
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
| `SZARRAY`, and `ARRAY` with rank only (sizes and lower bounds not yet) | partial | partial | arrays-sum, multidim-arrays |
| `PTR`, `BYREF` (`FNPTR`, `TYPEDBYREF` not yet)                   | partial | partial |         |
| `GENERICINST`, `VAR`, `MVAR`                                     | partial | partial | generic-calls |
| `CMOD_REQD`, `CMOD_OPT`                                          | none | none    |         |
| TypeSpec and MethodSpec blobs (II.23.2.14, II.23.2.15)           | partial | partial | generic-calls |
| Custom attribute value blobs (II.23.3)                           | partial | partial | custom-attrs (literal bytes from `.custom`, not typed; only the 0x0001 prolog is checked) |
| Marshalling descriptors (II.23.4)                                | none | none    |         |

## Flags and enumerations (II.23.1)

| Feature                                         | Write status | Fixture |
|-------------------------------------------------|--------------|---------|
| TypeAttributes (visibility, layout, semantics)  | partial (from keywords) |         |
| MethodAttributes and MethodImplAttributes       | partial (from keywords; `virtual`, `newslot`, `final`, `abstract` done, see `virtual-override`) | virtual-override |
| FieldAttributes                                 | constants only (`flags.rkt`), not wired to ilasm | |
| ParamAttributes                                 | constants only (`flags.rkt`), not wired to ilasm | |
| AssemblyFlags and AssemblyHashAlgorithm         | none         |         |
| PInvokeAttributes                               | partial (calling convention, charset, SupportsLastError from `pinvokeimpl`; `flags.rkt`) | pinvoke |
| GenericParamAttributes                          | none         |         |

Parse ilasm keyword lists (`(public static hidebysig)`) into these flag values instead of writing literals.

## Method bodies and IL (II.25.4, Partition III)

Tracked in [opcodes.md](opcodes.md). Summary: every opcode in the shared table (`src/il/opcodes.rkt`) can be encoded, and the lint decodes all of them. Tiny and fat headers, `.locals` (LocalVarSig), and computed maxstack are done. Catch, finally, fault, and `filter` EH are done, and prefix validation is in. The `il-all-opcodes` fixture covers the verifiable opcodes, including the box, field-address, type-token, constrained, and `ldftn` groups. `il-unverifiable-opcodes` covers `jmp`, `ldvirtftn`, and the unverifiable ops (PEVerify `/md` only). `il-runtime-only-opcodes` covers `mkrefany`, `refanyval`, and `calli`, which no verifier accepts, so it is checked by running only. The `ops-*` fixtures run arithmetic, branches, constants, conversions, locals and args, and EH.

## Module and type model

| Feature                                                    | Status  | Fixture |
|------------------------------------------------------------|---------|---------|
| Multiple classes with namespaces, class-typed fields, parameters, and returns | done | multi-types |
| `extends` to a same-module class or an external class (`System.Object` by default), with base ctor chaining and inherited field and method access | done | extends-base |
| `extends` (`System.ValueType`, `System.Enum`) for value types and enums | partial (value types done: `System.ValueType` base, by-value args and returns, `ldloca`, `initobj`; enums not) | value-types |
| Static methods, same-module calls (forward and recursive), parameters | done | calls-multi |
| Static fields (same module)                                | done    | `static-fields` |
| Instance fields (same module: `ldfld`, `stfld`, `ldflda`), `.ctor` | done | instance-methods, il-all-opcodes |
| Instance fields on external types (`ldfld`, `stfld`, `ldflda` on a MemberRef FieldSig) | done | external-instance-field |
| `.cctor` type initializer (static, specialname, rtspecialname; no beforefieldinit unless requested) | done | cctor-init |
| Instance methods, `newobj`, `callvirt`                     | done    | instance-methods |
| Virtual methods (`virtual`, `newslot`, `final`, `abstract`; body-less abstract methods) and virtual dispatch through `callvirt` on a base-typed reference (II.10.3) | done | virtual-override |
| `.override Base::M` (same-module base or external base MemberRef), MethodImpl row (II.22.27) | done (base must be an ancestor; external base's virtual flag not checked) | virtual-override |
| Interfaces and implementation (interface TypeDef, `.implements` with same-module or external interfaces, InterfaceImpl rows II.22.23, signature-matched implementation check) | done | interfaces |
| Nested types (`nested public\|private\|assembly\|family\|famandassem\|famorassem` inside a class body; NestedClass rows; no namespace on the TypeDef) | done | nested-types |
| Properties and events                                      | none    |         |
| Generic types and methods (generic instances, same-module generic calls) | partial | generic-calls |
| Single-dimension arrays (`newarr`, `ldelem`, `stelem`, `ldlen`; `ldelema` unit-tested only) | done | arrays-sum |
| Multi-dimensional arrays `(array ELEM RANK)` with `.ctor`, `Get`, `Set`, `Address` as `call instance` on a TypeSpec parent (II.14.2, II.23.2.13); bounded form (sizes, lower bounds) rejected | done | multidim-arrays |
| Value types and enums (enum `value__` and literal fields with Constant rows) | done | enum-literals, value-types |
| Custom attributes: `.custom` on the assembly, a class, or a method, with a same-module or external constructor and a literal hex blob (II.22.10, II.23.3). Blobs are written as given, not typed | done | custom-attrs |
| P/Invoke (static, body-less `pinvokeimpl` with DLL, calling convention, optional charset and lasterr, entry point `as`; PreserveSig set) | done (instance P/Invoke rejected) | pinvoke |
| Multiple assembly references with versions and public key tokens | done | asm-refs-versioned |
| Entry point token taken from `.entrypoint`                 | done    | nano    |
| `<Module>` members move to a generated `Program` class (`parse-il`). Helpers must live in a named class, not `<Module>`. Kept for now; future option: resolve `<Module>` references to `Program` (changes snapshots) | done | nano |
| Static data (`.data`, FieldRVA)                            | done    | static-data |
| Embedded managed resources (`.mresource`, ManifestResource, CLI resources blob) | done | managed-resources |


## PE image (II.25, PE/COFF)

| Feature                                              | Read    | Write   | Fixture |
|------------------------------------------------------|---------|---------|---------|
| PE32, x86 `ILONLY` EXE                               | done    | partial |         |
| DLL output (`IMAGE_FILE_DLL`, `_CorDllMain`)         | n/a     | done    | dll-output |
| PE32+ (AMD64, ARM64), import stub `movabs`+DIR64    | partial (AMD64 writer via `nano-x64`; ARM64 out of scope) | out of scope |     |
| AnyCPU, `32BITREQUIRED`, and `32BITPREFERRED` (`.platform anycpu\|x86\|32bitpreferred`) | n/a | done | platform-x86 |
| Subsystem GUI versus console (`.subsystem console\|windows`) | n/a | done | subsystem-gui |
| Multiple sections (`.text`, `.rsrc`, `.reloc`, `.sdata`) | partial | partial (`.text`, `.reloc`, `.sdata` when there is static data) | static-data |
| Sections of any size (no 0x400 limit)                | done    | done    | text-over-400, text-over-2000 |
| Base relocations generated from fixups               | n/a     | done    | base-relocs |
| Deterministic timestamp and MVID                     | n/a     | done    | nano    |
| Debug directory and portable PDB                     | out of scope | out of scope |     |
| Win32 resources (version info, manifest)             | none    | done    | win32-resources |
| Strong-name signature                                | out of scope | out of scope |     |
| .NET (Core) target with `runtimeconfig.json`         | out of scope | out of scope |     |

## Suggested order

1. Static fields are done (`static-fields`). Instance methods, `.ctor`, `newobj`, and same-module instance fields are done (`instance-methods`, `il-all-opcodes`). External instance calls use the `instance` keyword, as in ilasm: `(call instance int32 (mscorlib System.String) get_Length ())`. The keyword sets HASTHIS in the MemberRef signature. Without it, a non-virtual call to an external instance method is still lowered as static, so the runtime call fails; a same-module `instance` on a static method is rejected (`instance-external-call`). `.cctor` is done (`cctor-init`), and external instance fields are done (`external-instance-field`). Locals, fat bodies, branching, catch, finally, fault, and filter EH are done. The `ldstr` hello world and `switch` fixtures are done. Virtual methods, body-less abstract methods, and `.override` (MethodImpl) are done (`virtual-override`).
3. Multiple types with namespaces, extends, and nested types are done. Interfaces and implementation are done (`interfaces`). Interface inheritance and MethodImpl routing for interfaces are not.
4. Value types, enums, static data. Single-dimension arrays are done (`arrays-sum`); multi-dimensional arrays with rank only are done (`multidim-arrays`); bounded multi-dimensional arrays are not. Static data is done (`static-data`). Syntax: a static field takes its initial bytes from a top-level `.data` block, `(.data D_Table = (bytearray (01 00 00 00)))` with hex bytes, and the field names it with `at`, `(.field (public static) int32 Table at D_Table)`. This is the ilasm spelling, so the `bytes` keyword is rejected. The length must equal the primitive's size, and each block belongs to one field. The field gets HasFieldRVA and a FieldRVA row (II.22.18) whose RVA points into the `.sdata` section (II.16). A literal field cannot have data.
5. Generics: generic methods, TypeSpec, MethodSpec, GenericParam are done. GenericParamConstraint and generic types are not.
6. Properties, events, constants.
7. DLL output and AnyCPU for Framework targets.
8. P/Invoke is done (`pinvoke`): `pinvokeimpl` methods lower to ModuleRef, ImplMap, and MethodDef rows with PinvokeImpl and PreserveSig. Win32 resources are not. PDB, strong naming, ARM64, and .NET (Core) are out of scope until requested. PE32+ (AMD64) output is covered by `nano-x64`.
