---
title: Rangi architecture
description: Current state of the Rangi code, known defects and hardcoded values, and the target module layering
ms.date: 2026-10-17
---

## Current state (October 2026)

All code lives in `src/` as four Racket files. Five commits exist; the latest (`c29eb32`) makes the writer compute the `.text` size. The working tree has uncommitted changes to `cli-writer.rkt` and `cli-writer-test.rkt`.

| File                      | Role today                                                                                                   |
|---------------------------|--------------------------------------------------------------------------------------------------------------|
| `src/cli-reader.rkt`      | Lazy PE + CLI metadata reader. Exports `read-file`, `get-public-typedefs`, `read-assembly-meta`.             |
| `src/cli-writer.rkt`      | s-expression ilasm front end (`parse-il`) and a monolithic `assemble` that writes `c:\temp\rangi.exe`.       |
| `src/cli-writer-test.rkt` | Not a test. A typed mini-compiler experiment (`il-module`, `compute-t`, `fancy-add`) that drives the writer. |
| `src/cli-test.rkt`        | Experiment that loads `mscorlib.dll` at phase 1 with `add-ref`.                                              |

Baseline behaviour: `racket src/cli-writer-test.rkt` writes a 2048-byte image that runs and prints `203`. `PEVerify /md /il` reports one metadata warning: `Internal error: 0x8013129d [token:0x06000001]`.

### Reader

`read-file` reads the whole file into a byte string, then parses the DOS header, COFF header, PE32 optional header, section headers, CLI header, metadata root, and stream headers. It copies each heap, computes heap index widths, simple and coded index widths, then the row size and file offset of every table. Rows are decoded only on demand.

Known defects:

* Only PE32 is parsed. PE32+ (`magic = 0x20B`, used by x64 and many modern assemblies) misreads every field after `base-code`.
* The table-id switch omits `FieldPtr` (0x03), `MethodPtr` (0x05), `ParamPtr` (0x07), `EventPtr` (0x13), `PropertyPtr` (0x16), `ENCLog` (0x1E), `ENCMap` (0x1F), `AssemblyProcessor` (0x21), `AssemblyOS` (0x22), `AssemblyRefProcessor` (0x24), and `AssemblyRefOS` (0x25). Any assembly containing them raises an error.
* The row-size `case` has no `standalonesig` (0x11) entry, so any assembly with local variables raises `unknown type standalonesig`.
* The `#-` (uncompressed) stream name is rejected, and the `HeapSizes` 0x20/0x40 bits (extra data) are ignored.
* `HasCustomAttribute` lists `permission` instead of `declsecurity`.
* `get-public-typedefs` tests `(bits-set? 1 flag)`. Visibility is a 3-bit field (`flags & 0x7`), so this also matches `NestedFamily` (3), `NestedFamANDAssem` (5), and `NestedPublic` (7).
* `read-file` never closes its input port.
* Row layouts are written by hand and duplicated in the writer.

### Writer

`parse-il` walks the s-expression program and collects strings, type references, and member references into mutable hashes. `assemble` then builds heaps, assembles IL, and writes the whole PE file in one function of about 700 lines.

Hardcoded or broken behaviour, all of which must go:

* Output path `c:\temp\rangi.exe`; stray `writeln` debug output.
* The DOS stub, COFF header, NT fields, and section headers are literal byte vectors. Timestamp `0x6844FF0C`, `SizeOfCode = 0x400`, `.reloc` at RVA `0x4000`, and an error when `.text` reaches `0x400` bytes.
* The `#~` header writes a fixed `Valid` mask (`0x0900000447`), a fixed `Sorted` mask, and seven row counts of `1`. Stream size is `tables + 24 + 28 + 4`, metadata size uses a literal `0x6C`, and six "mysterious padding bytes" follow the tables.
* Metadata version string, stream header block (`0x4C`), import table, hint/name table, entry stub `FF 25`, and the relocation target (`0x402000`) are fixed.
* The entry point token is fixed at `0x06000001`; the module MVID GUID is a constant.
* `TypeRef.ResolutionScope`, `MemberRef.Class`, `TypeDef.Extends`, `FieldList`, `MethodList`, `ParamList`, and all flag columns are literals.
* Row order and heap order come from iterating mutable hashes, so output is not deterministic once there is more than one item.
* `write-br` checks `ss` (string width) instead of `bs` (blob width).
* `max-asm-ref-index` calls `max` on a list, and `ref-assembly` stores `max-index` instead of `index`.
* The `#US` heap is seeded with an unexplained `00 03 32 00 00` entry.
* `calc-size` has no `standalonesig` entry.
* Method bodies are always tiny headers (no locals, maxstack 8, code under 64 bytes).
* Only `ret`, `add`, `ldc.i` (always `ldc.i4`), and `call` of a `MemberRef` are assembled; anything else is silently skipped.
* Signatures support only `void`, `int32`, and `object`.

## Target layering

The core rule: the PE image layer knows nothing about CLI metadata, and the metadata layer knows nothing about file offsets.

```text
rangi/
  private/binary.rkt        little/big-endian ints, alignment, compressed ints, byte builders
  pe/
    model.rkt               image, section, chunk, symbol, fixup structs
    layout.rkt              assigns file offsets and RVAs; emits a layout map
    write.rkt               serialises headers, sections, data directories
    read.rkt                parses headers and sections; rva->offset
    imports.rkt             mscoree import + IAT + entry stub chunks (x86, x64, AnyCPU)
    relocs.rkt              base relocation chunk built from fixups
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

A section is an ordered list of chunks. Each chunk has a name, an alignment, and either fixed bytes or a size plus a writer procedure. Chunks may define symbols (for example `cli-header`, `metadata-root`, `method:Program::Main`) and may contain fixups that reference symbols as RVA, VA (needs a base relocation), or file offset. Layout runs in two passes: assign sizes and positions, then serialise with fixups resolved. Data directories reference symbols, not numbers. The layout pass also produces a text layout map for snapshots.

### CLI layer contract

The CLI layer builds a module model (assembly, module, refs, typedefs, members, bodies), then produces three kinds of chunks: IL method bodies (RVA symbols per method), the metadata blob, and the CLI header. Optional chunks cover field RVA data, managed resources, and the strong-name signature. Metadata tokens are known before layout. RVAs inside metadata (`MethodDef.RVA`, `FieldRVA.RVA`) are fixups resolved by the PE layer.
