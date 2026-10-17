---
title: Verification plan
description: How Rangi verifies emitted PE/CLI images and their layout as the code changes, using snapshots, internal invariants, and external .NET oracles
ms.date: 2026-10-17
---

## Goal

Any change that alters an emitted image must fail a test until a person reviews and approves the difference. Separately, every image must satisfy the ECMA-335 and PE/COFF rules as judged by tools we did not write.

## Prerequisite: determinism

Status: done in V0 (`ca7aa13`). The list below is what determinism requires:

* Replace hash iteration with insertion-ordered collections (for example a `gvector` plus an index `hash`) for heaps, rows, and methods.
* Take the COFF timestamp from an option. Deviation: the timestamp is always `0`; there is no option yet.
* Derive the module MVID from a content hash (for example the first 16 bytes of SHA-256 over the metadata with the MVID zeroed).

## Verification layers

Each fixture runs through every layer. A fixture is a directory under `tests/fixtures/<name>/` that contains a `program.rktd` (Rangi s-expression), an optional `expected-stdout.txt`, and approved snapshots.

### L1 Unit tests (rackunit)

Fast, pure tests in `tests/unit/`:

* Little-endian writers, alignment, and compressed unsigned and signed integers (II.23.2), including the boundary values `0x7F`, `0x80`, `0x3FFF`, `0x4000`, and `0x1FFFFFFF`
* Coded index width thresholds for every coded index kind in `cli/schema.rkt` (row counts at `2^(16-tagbits) - 1` and one above)
* Signature encoding for each element type
* Opcode encodings (see [opcodes.md](opcodes.md))
* Layout engine: alignment, RVA and file offset assignment, fixup resolution

### L2 Layout map snapshot

`pe/layout.rkt` emits a text map for every image, approved as `layout.txt`:

```text
section .text  rva 0x2000 vsize 0x01D4 file 0x0200 rawsize 0x0200 flags CNT_CODE|MEM_EXECUTE|MEM_READ
  0x2000 0x0200 0x0008 iat
  0x2008 0x0208 0x0048 cli-header
  0x2050 0x0250 0x000C il:<Module>::main
  0x205C 0x025C 0x0170 metadata
    +0x0000 0x20 root  +0x006C 0xC4 #~  +0x0130 0x28 #Strings ...
datadir IMPORT  0x21C8 0x0053
datadir CLI     0x2008 0x0048
```

The map is the main tool for reviewing layout changes. It is human-readable, diffs well in git, and shows immediately when a chunk moves or grows.

### L3 Metadata dump snapshot

A canonical, text dump of every metadata table row, heap entry, and decoded signature, produced by Rangi's own reader (`src/cli-reader.rkt`), approved as `metadata.txt`. This dump also serves as the reader's round-trip test.

### L4 Image hash snapshot

The SHA-256 of the emitted image, approved as `image.sha256`. It catches byte changes that L2 and L3 miss, such as padding or header fields.

### L5 Internal invariant checker (`tests/lib/pe-lint.rkt`)

The checker parses the raw bytes itself, so a reader bug cannot hide a writer bug. Table layouts come from the L3 decoder, and row offsets and sizes come from the reader and are checked against the bytes. `tests/image-lint-test.rkt` runs it on every fixture and on damaged copies of one image. It asserts:

* PE: PE32 magic and i386 machine; DOS header starts with `MZ`; `e_lfanew` and the PE signature; COFF `EXECUTABLE_IMAGE` set and `RELOCS_STRIPPED` clear when a base relocation directory exists; subsystem is Windows GUI or console; `FileAlignment` and `SectionAlignment` are powers of two; `ImageBase` is 64K aligned; `SizeOfHeaders` is the header size rounded up; `SizeOfCode`, `SizeOfInitializedData`, `BaseOfCode`, `BaseOfData`, and `SizeOfImage` match the section table; sections are aligned, non-overlapping, in order, readable, and have raw data inside the file; every data directory lies inside a section
* Entry: `AddressOfEntryPoint` is in a code section that is readable and executable, is an `FF 25` jump through the import address table, and a base relocation covers its operand; the import descriptor names `mscoree.dll` and the first import is `_CorExeMain`
* CLI: header size 0x48, ILONLY flag set, metadata inside a section, entry token is a MethodDef row
* Metadata: `BSJB` root and version 1.1; streams are 4-byte aligned, inside the blob, and unique; `#Strings`, `#Blob`, and `#GUID` sizes equal the reader's heap lengths; heap index widths agree with the `HeapSizes` bits; `Valid` has no bits above II.22; row counts agree with the reader; tables are contiguous; at most 3 bytes of trailing padding
* Rows: every string, blob, and GUID index is in range; every simple index is at most the target row count plus one (list starts may point past the last row); every coded index has a valid tag and an in-range row
* Method bodies: tiny or fat headers; code inside the file; instructions decode and end exactly at the code size; each `call` target row exists

Deviations from the original plan:

* The writer emits `Sorted = 0` and rows in insertion order, so the sorted-by-key and list-monotonic checks are not applied. The CLR does not require sorted tables, and PEVerify accepts them.
* Field and param rows are checked by count only, because the L3 decoder does not decode them.
* The IL decoder accepts only `ret`, `add`, `ldc.i4`, and `call` (MemberRef or MethodDef). Any other opcode is reported, so a new opcode needs a decoder here before it is emitted.

### L6 External oracles

Each oracle is a script under `tests/oracles/` and is skipped when the tool is missing, with a message. Set `RANGI_REQUIRE_ORACLES=1` to make a missing tool an error instead. Use that on a machine that is supposed to have the full toolchain, so the oracles cannot pass by skipping.

| Oracle                               | Catches                                                     | Command                                                         |
|--------------------------------------|-------------------------------------------------------------|-----------------------------------------------------------------|
| PEVerify (.NET Framework SDK)        | Metadata validation (`/md`) and IL type safety (`/il`)      | `PEVerify.exe /md /il /nologo <image>`                          |
| ildasm                               | Readable disassembly; snapshot as `ildasm.il` after scrubbing timestamp, MVID, and image base comments | `ildasm.exe /all /text /nobar <image>` |
| System.Reflection.Metadata dumper    | Independent table decoder; diff against L3                  | `dotnet run --project tests/oracles/srm-dump/srm-dump.csproj -- <image>` |
| ILVerify (`Microsoft.ILVerification`) | IL verification that also works for .NET (Core) targets    | Not implemented: `tests/oracles/ilverify` does not exist yet    |

The baseline PEVerify warning (`0x8013129d` on `MethodDef` 1) is fixed. `main` sat on the `<Module>` type, and ilasm assembles the same code with no warning when `main` is inside a class. The writer now moves `<Module>` methods into a generated `Program` class, and `pe-verify.txt` records a clean run.

### L7 Execution

Run the image and compare stdout and exit code with `expected-stdout.txt`. Images run directly under .NET Framework. .NET (Core) runs are out of scope.

### L8 Differential comparison with ilasm

For fixtures that have an equivalent `program.il`, assemble it with `ilasm.exe` and compare the SRM dumps of both images with row order normalised. Byte equality is not expected, but table contents, signatures, and IL bytes should match. Disagreements point at encoding bugs.

## Snapshot workflow

* `raco test tests/` runs every layer and fails on any snapshot difference, printing a unified diff.
* `RANGI_UPDATE_SNAPSHOTS=1 raco test tests/` rewrites snapshots. Commit them with an explanation of why bytes or layout changed.
* Snapshots live beside their fixture so a single diff shows program, layout, metadata, and disassembly changes together.

## Milestones

* [x] V0 Determinism: tables and heaps keep insertion order, the MVID is a content hash, and the COFF timestamp is 0. Deviation: there is no timestamp option. Checked by building the same program under two directories and comparing SHA-256; the L4 snapshot enforces it afterwards.
* [x] V1 Harness skeleton: `tests/` tree, fixture runner, L4 hash and L7 execution for the current `42` program (`experiments/nano.rkt`; hash in `tests/fixtures/nano/image.sha256`)
* [x] V2 External oracles: PEVerify and ildasm scripts; `0x8013129d` triaged and fixed (see L6)
* [x] V3 SRM dumper (small .NET console project) and L3 dump from Rangi's reader, diffed against each other

Deviations recorded for P1:

* L3 covers table rows only. Heap entries and decoded signatures are not yet checked.
* The diff is a `check-equal?` failure rather than a unified diff printer.
* The row decoder lives in `tests/lib/metadata-dump.rkt` until P2 moves it into `cli/schema`.
* `src/cli-reader.rkt` gains read-only accessors and stores the encoding sizes it already computes. It does not change the lazy lookup path.
* mscorlib is compared by public type count only (1521, equal to SRM), because the L3 decoder still throws on tables it does not decode yet (TypeSpec, CustomAttribute, GenericParam, and others). MethodSpec rows are decoded and match SRM (656 rows on mscorlib).
* The PE32+ reader output was compared with SRM by hand on an `ilasm /X64` image. No fixture covers it yet.
* [x] V4 L5 invariant checker (`tests/lib/pe-lint.rkt`, `tests/image-lint-test.rkt`); deviations listed under L5
* [ ] V5 L2 layout map (lands with restructure R3, when the layout engine exists)
* [ ] V6 L8 ilasm differential fixtures for every feature in [cli-coverage.md](cli-coverage.md)
* [ ] V7 Reader corpus test: run the L3 dump against every assembly in the .NET Framework 4.7.1 reference set and `System.Private.CoreLib`, diffed against SRM

## Spec sources and discovery

Source order for facts about the metadata format:

1. System.Reflection.Metadata (SRM) and CoreCLR in dotnet/runtime. The reader must agree with SRM on every reference assembly. The SRM oracle (`tests/oracles/srm-dump`) is the check.
2. The ECMA-335 6th edition text, as transcribed in the stakx/ecma-335 markdown. II.24.2.1 and II.24.2.6 define the `#~` header and the HeapSizes bits 0x01, 0x02, and 0x04. They do not mention `#-`, 0x20, or 0x40.
3. Web search summaries. They contradicted each other on `#-` and extra data, so no rule is taken from them.

Findings from SRM (`src/libraries/System.Reflection.Metadata/src/System/Reflection/Metadata/`):

* `Internal/COR20Constants.cs`: `#-` is the uncompressed table stream. `#JTD` is the minimal-delta stream and `#Pdb` is the standalone PDB stream.
* `MetadataReader.cs`: `#-` sets `MetadataStreamKind.Uncompressed`. The compressed kind (`#~`) rejects pointer tables and EncMap, and the uncompressed kind allows them. Index widths depend on row counts and minimal delta, not on the kind.
* `Internal/MetadataFlags.cs`: `HeapSizes.ExtraData = 0x40`. When it is set, SRM reads and skips 4 bytes right after the row counts. Its comment says the CLI spec does not mention this, but the native reader honours it. SRM does not test 0x20.
* The stream switch has `default: continue` with the comment "Some obfuscators insert invalid streams". Unknown streams are skipped, not errors.

Local corpus scan (roadmap item 1):

* A byte search for `#-` followed by NUL found 525 candidate files in the .NET Framework directories, the reference assemblies, and the .NET runtimes. The reader parsed each one.
* 485 parsed with only known streams. None contained a real `#-` stream.
* 34 failed with `rva 0x0 is not in any section`. These are native binaries with no CLI header.
* 6 failed with unknown stream `#!`. They are NGEN native images: `mscorlib.ni.dll`, `system.ni.dll`, and `system.core.ni.dll` under `NativeImages`, in both `Framework` and `Framework64`.
* So the local machine has no sample of `#-` or of the 0x40 flag. Test those with a patched image or a sample from another source.

Patched-image check (roadmap item 1): `tests/lib/patch-image.rkt` turns the nano `#~` image into a `#-` image with HeapSizes 0x40 and the 4 extra bytes. It fixes up the stream offsets, the MethodDef and FieldRVA RVAs, the entry point, the import directory, and the base relocations, then removes the same number of zero padding bytes from `.text`, so the file size is unchanged. `tests/stream-variants-test.rkt` checks three things. The patched image runs and prints 42. Its dump matches the `#~` dump apart from `Rva=` values. A copy with the `#US` stream renamed to `#!` gives the same dump. SRM agrees with the reader on both patched images. The CLR loads and runs the patched `#-` image, but this is one small program, so it does not show that every `#-` image in the wild has the same layout.
Tooling: `search_code` on dotnet/runtime finds the SRM paths. Read a file from `raw.githubusercontent.com/dotnet/runtime/main/<path>` to get its full text.
