---
title: Verification plan
description: How Rangi verifies emitted PE/CLI images and their layout as the code changes, using snapshots, internal invariants, and external .NET oracles
ms.date: 2026-10-17
---

## Goal

Any change that alters an emitted image must fail a test until a person reviews and approves the difference. Separately, every image must satisfy the ECMA-335 and PE/COFF rules as judged by tools we did not write.

## Prerequisite: determinism

Snapshots only work if output is reproducible. Before V1 snapshots are trusted:

* Replace hash iteration with insertion-ordered collections (for example a `gvector` plus an index `hash`) for heaps, rows, and methods.
* Take the COFF timestamp from an option. Default to `0`, or to a hash of the image content as Roslyn's `/deterministic` does.
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

A canonical, text dump of every metadata table row, heap entry, and decoded signature, produced by Rangi's own reader (`cli/reader.rkt`), approved as `metadata.txt`. This dump also serves as the reader's round-trip test.

### L4 Image hash snapshot

The SHA-256 of the emitted image, approved as `image.sha256`. It catches byte changes that L2 and L3 miss, such as padding or header fields.

### L5 Internal invariant checker (`tests/lib/pe-lint.rkt`)

The checker parses the image with `pe/read.rkt` and asserts:

* `e_lfanew`, section alignment, file alignment, `SizeOfHeaders`, `SizeOfImage`, `SizeOfCode`, `SizeOfInitializedData`, `BaseOfCode`, and `AddressOfEntryPoint` are consistent with the section table
* Sections are sorted, non-overlapping, aligned, and `VirtualSize <= SizeOfRawData` rounded up
* Every data directory and CLI header RVA falls inside a section
* The base relocation block covers the entry stub's absolute address
* Metadata stream offsets and sizes are 4-byte aligned and inside the metadata blob
* The `Valid` mask matches the tables that have rows; row counts and row sizes match the `#~` length
* Sorted tables (II.22, "sorted" column) are sorted by their primary key, and `Sorted` bits are set for them
* Every heap index, simple index, and coded index is in range; list columns (`FieldList`, `MethodList`, `ParamList`) are monotonic
* Every IL token resolves to an existing row, and every method body's code size matches its header

### L6 External oracles

Each oracle is a script under `tests/oracles/` and is skipped when the tool is missing.

| Oracle                               | Catches                                                     | Command                                                         |
|--------------------------------------|-------------------------------------------------------------|-----------------------------------------------------------------|
| PEVerify (.NET Framework SDK)        | Metadata validation (`/md`) and IL type safety (`/il`)      | `PEVerify.exe /md /il /nologo <image>`                          |
| ildasm                               | Readable disassembly; snapshot as `ildasm.il` after scrubbing timestamp, MVID, and image base comments | `ildasm.exe /all /text /nobar <image>` |
| System.Reflection.Metadata dumper    | Independent table decoder; diff against L3                  | `dotnet run --project tests/oracles/srm-dump -- <image>`        |
| ILVerify (`Microsoft.ILVerification`) | IL verification that also works for .NET (Core) targets    | `dotnet run --project tests/oracles/ilverify -- <image>`        |

PEVerify already finds one issue in today's baseline (`0x8013129d` on `MethodDef` 1), so the first V2 task is to triage and fix it.

### L7 Execution

Run the image and compare stdout and exit code with `expected-stdout.txt`. Images run directly under .NET Framework. .NET (Core) runs are out of scope.

### L8 Differential comparison with ilasm

For fixtures that have an equivalent `program.il`, assemble it with `ilasm.exe` and compare the SRM dumps of both images with row order normalised. Byte equality is not expected, but table contents, signatures, and IL bytes should match. Disagreements point at encoding bugs.

## Snapshot workflow

* `raco test tests/` runs every layer and fails on any snapshot difference, printing a unified diff.
* `RANGI_UPDATE_SNAPSHOTS=1 raco test tests/` rewrites snapshots. Commit them with an explanation of why bytes or layout changed.
* Snapshots live beside their fixture so a single diff shows program, layout, metadata, and disassembly changes together.

## Milestones

* [ ] V0 Determinism: ordered collections, timestamp option, content-derived MVID
* [ ] V1 Harness skeleton: `tests/` tree, fixture runner, L4 hash and L7 execution for the current `42` program (`experiments/nano.rkt`, SHA-256 `D0CB3275...`)
* [ ] V2 External oracles: PEVerify and ildasm scripts, triage the `0x8013129d` warning
* [ ] V3 SRM dumper (small .NET console project) and L3 dump from Rangi's reader, diffed against each other
* [ ] V4 L5 invariant checker
* [ ] V5 L2 layout map (lands with restructure R3, when the layout engine exists)
* [ ] V6 L8 ilasm differential fixtures for every feature in [cli-coverage.md](cli-coverage.md)
* [ ] V7 Reader corpus test: run the L3 dump against every assembly in the .NET Framework 4.7.1 reference set and `System.Private.CoreLib`, diffed against SRM
