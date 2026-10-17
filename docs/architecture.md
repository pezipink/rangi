---
title: Rangi architecture
description: Current state of the Rangi code, known defects and hardcoded values, and the target module layering
ms.date: 2026-10-17
---

## Current state (October 2026)

All code lives in `src/`, with the experiments in `experiments/` and the test harness in `tests/`. The root `info.rkt` declares the `rangi` package. The WIP typed-expression experiment and its writer edits are in `stash@{0}` ("typed-expr experiment and debug edits").

| File                           | Role today                                                                                                   |
|--------------------------------|--------------------------------------------------------------------------------------------------------------|
| `src/cli-reader.rkt`           | Lazy PE + CLI metadata reader. Exports `read-file`, `get-public-typedefs`, `read-assembly-meta`, and read-only accessors used by tests. |
| `src/cli-writer.rkt`           | s-expression ilasm front end (`parse-il`) and `assemble`, which writes a deterministic PE image. Takes an optional output path (default a temp file). |
| `src/log.rkt`                  | The `rangi` logger used by the writer for debug and warning output.                                          |
| `tests/lib/pe-lint.rkt`        | Structural checker (`lint-image`) for PE, CLI, metadata, and IL invariants. Used by `tests/image-lint-test.rkt`. |
| `experiments/nano.rkt`         | Assembles `nano` and `nano2` into the temp dir and runs them. Prints `42` and `84`.                          |
| `experiments/phase1-load.rkt`  | Experiment that loads `mscorlib.dll` at phase 1 with `add-ref`.                                              |

Baseline behaviour: `racket experiments/nano.rkt` writes a 2048-byte image that runs and prints `42`. The image's SHA-256 is recorded in `tests/fixtures/nano/image.sha256`. `PEVerify /md /il` reports no warnings for it.

### Reader

`read-file` reads the whole file into a byte string, then parses the DOS header, COFF header, PE32 optional header, section headers, CLI header, metadata root, and stream headers. It copies each heap, computes heap index widths, simple and coded index widths, then the row size and file offset of every table. Rows are decoded only on demand.

Known defects:

* The `HeapSizes` bit 0x20 is not defined by the spec or by SRM, and the reader does not handle it.
* Row layouts are written by hand and duplicated in the writer.

Fixed and covered by tests: the `#-` (uncompressed) stream name, which SRM reads as a table stream with the same row layout (it accepts pointer tables there); unknown streams such as `#!` (in NGEN native images), which are skipped as SRM does (`default: continue`); the HeapSizes extra-data bit 0x40, where the 4 bytes after the row counts are read and discarded as SRM does (`tests/stream-variants-test.rkt`). PE32+ parsing, the table-id switch for the pointer, ENC, and Assembly processor/OS tables (previously an error), `standalonesig`, `HasCustomAttribute` (`declsecurity`), public type visibility (`flags & 0x7`), the port leak, and the missing-Assembly case (`read-assembly-meta` returns `#f`). `read-file` reads the file once and does not cache, so each call costs one read.

### Writer

`parse-il` walks the s-expression program and collects strings, type references, and member references into mutable hashes. `plan-image` builds the heaps, assembles IL, and places every chunk with `pe/layout.rkt`. `assemble` then serialises the placed image with `pe/write.rkt`. `image-layout-report` prints the same plan as the layout map that each fixture snapshots as `layout.txt`.

The output is deterministic. Tables and heaps keep insertion order, the MVID is a content hash, and the COFF timestamp is 0. `<Module>` methods move into a generated `Program` class, which clears the PEVerify `0x8013129d` warning. Method bodies use a tiny header when the code is under 64 bytes and `.maxstack` is at most 8, and a fat header otherwise.

Known limits (planned gaps, not defects in code that is present):

* Only `ret`, `add`, `ldc.i4`, and `call` (to a MemberRef or MethodDef) are assembled. Any other instruction raises an error. The lint decodes the same four opcodes.
* Signatures support only `void`, `int32`, and `object`.
* Method bodies have no locals and no exception handling.
* Assembly and AssemblyRef versions are 0, and the `.assembly` name is ignored. The assembly name is the output basename.
* Field and param rows are written, but the lint checks only their counts.

## Target layering

The core rule: the PE image layer knows nothing about CLI metadata, and the metadata layer knows nothing about file offsets.

```text
rangi/
  private/binary.rkt        little-endian ints, alignment, pad-to (built)
  pe/
    model.rkt               image-params, section, chunk, fixup, digest, placement structs (built)
    layout.rkt              chunk and section model; RVAs, file offsets, layout map (built)
    write.rkt               headers, section table, sections, data directories by chunk name (built, PE32 only)
    read.rkt                parses headers and sections; rva->file-offset (built)
    imports.rkt             mscoree import, IAT, entry stub chunks (built, x86 only)
    relocs.rkt              base relocation chunk built from chunk relocs (built)
  cli/
    schema.rkt              table ids, columns, coded indexes (single source of truth)
    heaps.rkt               #Strings, #US, #GUID, #Blob builders with dedup
    tables.rkt              row builders, sorting rules, row-size calculation
    metadata.rkt            metadata root + stream headers -> one chunk
    signatures.rkt          II.23.2 blob encoders and decoders
    tokens.rkt              token encode/decode, coded index encode/decode
    header.rkt              CLI header (II.25.3.3) chunk
    reader.rkt              lazy metadata reader built on schema.rkt
  il/
    opcodes.rkt             Partition III opcode table (data)
    assembler.rkt           labels, branch relaxation, operand encoding
    body.rkt                tiny/fat headers, locals sig, EH sections
  ilasm/
    syntax.rkt              s-expression ilasm front end -> module model
  image.rkt                 glue: module model -> CLI chunks -> PE image
experiments/                typed compiler and phase-1 loading experiments
tests/                      rackunit suites, fixtures, snapshots, oracle tools
```

Data flows one way:

```text
ilasm s-expr -> module model -> cli/* (chunks + symbols) -> pe/layout -> pe/write -> bytes
                                                                      \-> layout map (snapshot)
bytes -> pe/read -> cli/reader -> model/dumps (round trip, verification)
```

### PE layer contract

A section is an ordered list of chunks. Each chunk has a name, an alignment, plain bytes, and a list of fixups. The bytes hold zeros in each field that depends on layout. A `fixup` is a typed 4-byte field at an offset, with a kind and a target chunk name: `rva32` writes the target's RVA, and `va32` writes the image base plus the target's RVA and needs a base relocation. A `digest` is a 16-byte field filled with the SHA-256 of spans of the chunk's rendered bytes, used for the MVID. Chunks name their targets, not numbers, so data directories refer to chunk names too. Layout runs in two passes: assign sizes and positions, then render each chunk by copying its bytes and filling its fixups and digests. The layout pass also produces a text layout map for snapshots. `va64` fixups (8 bytes, DIR64 relocation) are used by the PE32+ entry stub, which is `movabs rax, [IAT]; jmp rax` (`48 A1 <abs64> FF E0`). `FF 25` takes only a 32-bit operand, so it cannot reach an IAT above 4 GB. The stub operand needs a real DIR64 relocation. The CLR loader rejects a PE32+ image whose `.reloc` holds only ABSOLUTE padding. `file-offset` fixups (the chunk's file offset, 4 bytes) are supported by the layout engine and covered by unit tests, but the writer does not use them yet. The writer emits PE32 by default and PE32+ when a program says `(.format pe32+)`. Image bases are `#x400000` for PE32 and `#x140000000` for PE32+.

### CLI layer contract

The CLI layer builds a module model (assembly, module, refs, typedefs, members, bodies), then produces three kinds of chunks: IL method bodies (RVA symbols per method), the metadata blob, and the CLI header. Optional chunks cover field RVA data, managed resources, and the strong-name signature. Metadata tokens are known before layout. RVAs inside metadata (`MethodDef.RVA`, `FieldRVA.RVA`) are fixups resolved by the PE layer.
