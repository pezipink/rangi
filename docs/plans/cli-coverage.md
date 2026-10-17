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
| 0x03 | FieldPtr               | out of scope | n/a | Pointer table, used only in uncompressed metadata (`#-`), which is out of scope | |
| 0x04 | Field                  | partial | partial | Same-module fields from `.field` keywords and FieldSig; `ldsfld`/`stsfld` checked for static-ness and type. Instance fields have no positive fixture yet | static-fields |
| 0x05 | MethodPtr              | out of scope | n/a | Pointer table, used only in uncompressed metadata (`#-`), which is out of scope | |
| 0x06 | MethodDef              | partial | partial | Flags from keywords; ImplFlags 0; ParamList is the next free Param rid (per method); same-module `call` targets (`(call ret (Class) name (params))`, static only; forward calls and recursion) | calls-multi |
| 0x07 | ParamPtr               | out of scope | n/a | Pointer table, used only in uncompressed metadata (`#-`), which is out of scope | |
| 0x08 | Param                  | done    | done    | One row per named param, in method order; Sequence 1-based; flags from `(param [in] [out] [opt] TY NAME [= value])`; unnamed params get no row | param-constants |
| 0x09 | InterfaceImpl          | done | done | Sorted; `.implements` rows (same-module and external interfaces); interface inheritance (an interface's `.implements` lists the interfaces it extends) | interfaces, interface-inheritance |
| 0x0A | MemberRef              | partial | partial | Parent is the TypeRef of the call target                 |         |
| 0x0B | Constant               | done    | done    | Sorted; literal fields and param default values (II.23.1.15 blobs); parent is Field or Param; fdHasDefault/pa-hasdefault set | param-constants |
| 0x0C | CustomAttribute        | partial | partial | Sorted by Parent; `.custom` on assembly, class, and method parents; Module parent not supported. Value blobs are literal bytes (II.23.3 prolog checked), not typed | custom-attrs |
| 0x0D | FieldMarshal           | done    | done    | Sorted; simple form only: one NATIVE_TYPE (II.23.4) per field, `(.field (marshal NATIVE) TY name)`; no arrays, no custom marshalers | param-constants |
| 0x0E | DeclSecurity           | none    | none    | Out of scope for P5: needs permission-set blobs (XML or binary, II.22.11 and II.23.3)  |         |
| 0x0F | ClassLayout            | done    | done    | Sorted; `.pack` (0,1,2,4,...,128) and `.size` on explicit or sequential classes (II.22.8) | class-layout |
| 0x10 | FieldLayout            | done    | done    | Sorted; one row per field with `offset N` in an explicit class (II.22.16)  | class-layout |
| 0x11 | StandAloneSig          | done    | done    | LocalVarSig blobs in `sigs.rkt`; `calli` with fnptr args (`calli-fnptr`) and runtime-only `calli void ()` (`il-runtime-only-opcodes`) | ops-locals-args, calli-fnptr, il-runtime-only-opcodes |
| 0x12 | EventMap               | done    | done    | Sorted by parent                                         | props-events |
| 0x13 | EventPtr               | out of scope | n/a | Pointer table, used only in uncompressed metadata (`#-`), which is out of scope | |
| 0x14 | Event                  | done    | done    | Sorted; type is a module delegate TypeDef or an external TypeRef | props-events, events-delegate |
| 0x15 | PropertyMap            | done    | done    | Sorted by parent                                         | props-events |
| 0x16 | PropertyPtr            | out of scope | n/a | Pointer table, used only in uncompressed metadata (`#-`), which is out of scope | |
| 0x17 | Property               | done    | done    | Flags 0 unless specialname/rtspecialname; HASTHIS instance, indexers with params; HasDefault rejected (Constant is metadata-rows) | props-events, events-delegate |
| 0x18 | MethodSemantics        | done    | done    | Sorted by association; getter, setter, add, remove       | props-events |
| 0x19 | MethodImpl             | partial | partial | Sorted; `.override` rows (same-module and external base, and same-module or external interfaces in the class's implements closure); the body must be a virtual method of the class | virtual-override, interface-inheritance |
| 0x1A | ModuleRef              | partial | done    | One row per P/Invoke DLL, first-use order (II.22.31)     | pinvoke |
| 0x1B | TypeSpec               | partial | partial | Row helper and `read-row`; blob via `sigs.rkt` and reader; generic instance types | generic-calls |
| 0x1C | ImplMap                | partial | done    | Sorted by MemberForwarded; P/Invoke (II.22.22)           | pinvoke |
| 0x1D | FieldRVA               | done    | done    | Sorted; RVA of the static field's `.data` chunk in `.sdata` (II.22.18); read side tested | static-data |
| 0x1E | ENCLog                 | out of scope | n/a | Edit-and-continue table; we never emit edits | |
| 0x1F | ENCMap                 | out of scope | n/a | Edit-and-continue table; we never emit edits | |
| 0x20 | Assembly               | partial | partial | Version, flags (including retargetable), public key, and culture are zero; `retargetable` is emitted on AssemblyRef only | asm-refs-retargetable |
| 0x21 | AssemblyProcessor      | out of scope | n/a | Obsolete; we never emit it, and readers ignore it | |
| 0x22 | AssemblyOS             | out of scope | n/a | Obsolete; we never emit it, and readers ignore it | |
| 0x23 | AssemblyRef            | partial | partial | Name, version, and public key token come from `.assembly extern` (II.22.5); Flags (retargetable) are set, HashValue is zero, and full public keys are not written | asm-refs-versioned, asm-refs-retargetable |
| 0x24 | AssemblyRefProcessor   | out of scope | n/a | Obsolete; we never emit it, and readers ignore it | |
| 0x25 | AssemblyRefOS          | out of scope | n/a | Obsolete; we never emit it, and readers ignore it | |
| 0x26 | File                   | none    | none    | Out of scope for P5: multi-module assemblies (needs `.file` and a second module)  |         |
| 0x27 | ExportedType           | none    | none    | Out of scope for P5: type forwarders are not cheap (needs `.exptype` syntax and the implementation ref coded index), so not started | |
| 0x28 | ManifestResource       | done    | done    | Embedded managed resources; covered by `managed-resources`                  | managed-resources |
| 0x29 | NestedClass            | partial | done    | Sorted by NestedClass; one row per nested type, from textual nested `.class`; read back via `read-row` only | nested-types |
| 0x2A | GenericParam           | partial | partial | Sorted; written for module generic methods; secondary sort key unverified | generic-calls |
| 0x2B | MethodSpec             | partial | partial | Generic method instantiation; written for `call` with `inst`. Rows match SRM on mscorlib (656) | generic-calls |
| 0x2C | GenericParamConstraint | done | done | Sorted by Owner; written for generic type params (`class`, `valuetype`, `.ctor`, and class or interface constraints) | generic-types |

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
| PropertySig (0x08)                                               | partial | partial | props-events (instance, no params), events-delegate (indexer with param); static untested |
| LocalVarSig (0x07), including `PINNED` and `BYREF` (II.23.2.6)   | partial | partial | ops-locals-args |
| StandAloneMethodSig for `calli`                                  | none | none    |         |
| Primitive element types (`BOOLEAN` through `U`, `STRING`, `OBJECT`) | partial | partial | |
| `CLASS` and `VALUETYPE` with TypeDefOrRefOrSpec encoded tokens   | partial | partial |         |
| `SZARRAY`, and `ARRAY` with rank, sizes, and lower bounds (sizes and bounds each empty or one per dimension; the spec allows fewer) | done | partial | arrays-sum, multidim-arrays, bounded-arrays |
| `PTR`, `BYREF` (`FNPTR`, `TYPEDBYREF` not yet)                   | partial | partial |         |
| `GENERICINST`, `VAR`, `MVAR`                                     | partial | partial | generic-calls |
| `CMOD_REQD`, `CMOD_OPT`                                          | none | none    |         |
| TypeSpec and MethodSpec blobs (II.23.2.14, II.23.2.15)           | partial | partial | generic-calls |
| Custom attribute value blobs (II.23.3)                           | partial | partial | custom-attrs (literal bytes from `.custom`, not typed; prolog 0x0001 verified against II.23.3; NumNamed is not written by the code, the user's blob is literal. The System.Attribute base is a CLS rule (II.21), not checked) |
| Marshalling descriptors (II.23.4)                                | none | none    |         |

## Flags and enumerations (II.23.1)

| Feature                                         | Write status | Fixture |
|-------------------------------------------------|--------------|---------|
| TypeAttributes (visibility, layout, semantics)  | partial (from keywords) |         |
| MethodAttributes and MethodImplAttributes       | partial (from keywords; `virtual`, `newslot`, `final`, `abstract` done, see `virtual-override`) | virtual-override |
| FieldAttributes                                 | partial (`literal` and `static` keywords, `fdHasDefault` for literals, `fdHasFieldMarshal` and offsets for `.field` forms) | param-constants, class-layout |
| ParamAttributes                                 | partial (`in`, `out`, `opt`, HasDefault, HasFieldMarshal; `(param ...)` syntax) | param-constants |
| AssemblyFlags (retargetable) and AssemblyHashAlgorithm | partial | retargetable: asm-refs-retargetable; hash algorithm: none |
| PInvokeAttributes                               | partial (calling convention, charset, SupportsLastError from `pinvokeimpl`; `flags.rkt`). Values verified against II.23.1.8 (cdecl 0x0200, stdcall 0x0300, winapi = CallConvPlatformapi 0x0100, thiscall 0x0400, fastcall 0x0500). BestFit and ThrowOnUnmappableChar are not in the 2012 spec and are not written | pinvoke |
| GenericParamAttributes                          | partial (`class`, `valuetype`, `.ctor` specials; variance not). Values verified against II.23.1.7: class 0x0004, valuetype (NotNullableValueTypeConstraint) 0x0008, .ctor 0x0010. Covariant and contravariant are not written, and no GenericParamConstraint row is emitted for `valuetype` | generic-types |

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
| `.cctor` type initializer (static, specialname, rtspecialname; no beforefieldinit unless requested). Flags 0x1811 (private) are the spec-required set (II.10.5.3, II.22.26): Static, SpecialName, RTSpecialName. HideBySig (0x0080, csc emits 0x1891) is optional and not written | done | cctor-init |
| Instance methods, `newobj`, `callvirt`                     | done    | instance-methods |
| Virtual methods (`virtual`, `newslot`, `final`, `abstract`; body-less abstract methods) and virtual dispatch through `callvirt` on a base-typed reference (II.10.3) | done | virtual-override |
| `.override Base::M` (same-module base or external base MemberRef), MethodImpl row (II.22.27) | done (base must be an ancestor; the body must be virtual, II.22.27 rule 7; a same-module declaration must be virtual, rule 4; external base's virtual flag not checked; final, sealed, and strict-accessibility rules 5, 10, 11 not checked) | virtual-override |
| Interfaces and implementation (interface TypeDef, `.implements` with same-module or external interfaces, InterfaceImpl rows II.22.23, signature-matched implementation check, interface inheritance with transitive method checks, MethodImpl for inherited interface methods II.22.27) | done | interfaces, interface-inheritance |
| Nested types (`nested public\|private\|assembly\|family\|famandassem\|famorassem` inside a class body; NestedClass rows; no namespace on the TypeDef) | done | nested-types |
| Properties and events (`.property` with `getter`/`setter`, `.event` with `add`/`remove`, in a class body; a module delegate gets a sealed TypeDef with runtime `.ctor`/`Invoke`, and an external event type stays a TypeRef) | done | props-events, events-delegate |
| Generic types and methods (generic instances, same-module generic calls) | partial | generic-calls |
| Generic type definitions with type parameters and constraints (`class`, `valuetype`, `.ctor`, class or interface constraints), instantiated over int32 and a reference type | done | generic-types |
| Single-dimension arrays (`newarr`, `ldelem`, `stelem`, `ldlen`; `ldelema` unit-tested only) | done | arrays-sum |
| Multi-dimensional arrays `(array ELEM RANK)` with `.ctor`, `Get`, `Set`, `Address` as `call instance` on a TypeSpec parent (II.14.2, II.23.2.13); bounded form `(array ELEM RANK SIZES LOBOUNDS)` with the lower-bound and size `.ctor` (II.14.2) | done | multidim-arrays, bounded-arrays |
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
| PE `IMAGE_FILE_32BIT_MACHINE` (0x0100) is set iff the CLI header has `COMIMAGE_FLAGS_32BITREQUIRED` (II.25.2.2.1). Verified: AnyCPU images have COFF 0x0022 and COR flags 0x9. `32BITPREFERRED` (0x20000) is not in the 2012 spec and is taken from the runtime headers | n/a | done | the PE32 fixtures (snapshots regenerated, e.g. arrays-sum, dll-output/library) |
| Subsystem GUI versus console (`.subsystem console\|windows`) | n/a | done | subsystem-gui |
| Multiple sections (`.text`, `.rsrc`, `.reloc`, `.sdata`) | done | read side tested for `.text`, `.sdata`, `.reloc` (`static-data`) | static-data |
| Sections of any size (no 0x400 limit)                | done    | done    | text-over-400, text-over-2000 |
| Base relocations generated from fixups               | n/a     | done    | base-relocs. Block layout verified against II.25.3.2: one block per 4K page, dword-aligned blocks, 12-bit page offsets. A fixup's start address selects its block, so a 4-byte or 8-byte field may cross the page end. II.25.3.2 defines only HIGHLOW; DIR64 is PE/COFF and has no alignment rule there, so the import stub's unaligned DIR64 at offset 2 is allowed |
| Deterministic timestamp and MVID                     | n/a     | done    | nano    |
| Debug directory and portable PDB                     | out of scope | out of scope |     |
| Win32 resources (version info, manifest)             | none    | done    | win32-resources |
| Strong-name signature                                | out of scope | out of scope |     |
| .NET (Core) target with `runtimeconfig.json`         | out of scope | out of scope |     |

## Suggested order

1. Static fields are done (`static-fields`). Instance methods, `.ctor`, `newobj`, and same-module instance fields are done (`instance-methods`, `il-all-opcodes`). External instance calls use the `instance` keyword, as in ilasm: `(call instance int32 (mscorlib System.String) get_Length ())`. The keyword sets HASTHIS in the MemberRef signature. Without it, a non-virtual call to an external instance method is still lowered as static, so the runtime call fails; a same-module `instance` on a static method is rejected (`instance-external-call`). `.cctor` is done (`cctor-init`), and external instance fields are done (`external-instance-field`). Locals, fat bodies, branching, catch, finally, fault, and filter EH are done. The `ldstr` hello world and `switch` fixtures are done. Virtual methods, body-less abstract methods, and `.override` (MethodImpl) are done (`virtual-override`).
3. Multiple types with namespaces, extends, and nested types are done. Interfaces and implementation are done (`interfaces`). Interface inheritance and MethodImpl routing for interfaces are done (`interface-inheritance`).
4. Value types, enums, static data. Single-dimension arrays are done (`arrays-sum`); multi-dimensional arrays with rank, sizes, and lower bounds are done (`multidim-arrays`, `bounded-arrays`). Static data is done (`static-data`). Syntax: a static field takes its initial bytes from a top-level `.data` block, `(.data D_Table = (bytearray (01 00 00 00)))` with hex bytes, and the field names it with `at`, `(.field (public static) int32 Table at D_Table)`. This is the ilasm spelling, so the `bytes` keyword is rejected. The length must equal the primitive's size, and each block belongs to one field. The field gets HasFieldRVA and a FieldRVA row (II.22.18) whose RVA points into the `.sdata` section (II.16). A literal field cannot have data.
5. Generics: generic methods, TypeSpec, MethodSpec, GenericParam, and GenericParamConstraint are done (see `generic-types`). Generic types are done for same-module type definitions with constraints. Field access on generic instances from outside the class is done (`generic-field-access`, MemberRef with a TypeSpec GENERICINST parent, II.22.25). Method-level constraints are done in syntax (`method-constraints`, `(.typarams (T (class IArea)))` after a method name), and a constraint on a non-generic type or with the wrong argument count is a parse error. A type-variable operand such as `constrained. !!0` is a TypeSpec (II.22.39).
6. Properties, events, constants.
7. DLL output and AnyCPU for Framework targets.
8. P/Invoke is done (`pinvoke`): `pinvokeimpl` methods lower to ModuleRef, ImplMap, and MethodDef rows with PinvokeImpl and PreserveSig. Win32 resources are done (`win32-resources`): a `.win32resource` payload is laid out in the `.rsrc` section with data directory 2. PDB, strong naming, ARM64, and .NET (Core) are out of scope until requested. PE32+ (AMD64) output is covered by `nano-x64`.
