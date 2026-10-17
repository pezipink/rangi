---
title: Restructure plan
description: Steps for separating raw PE image creation from CLI metadata, sharing one table schema between reader and writer, and removing hardcoded layout
ms.date: 2026-10-17
---

## Target

See [architecture.md](../architecture.md#target-layering) for the module tree and the PE and CLI layer contracts. In short: `pe/` lays out sections of opaque chunks and resolves symbolic fixups, while `cli/` turns a module model into chunks. Neither layer reaches into the other's internals.

## Steps

Each step ends with `raco test tests/` green. R1 and R2 must not change any emitted byte (L4 hash unchanged). From R3 onward, snapshot changes are expected and must be explained.

### R1 Shared binary utilities

* [ ] Create `rangi/private/binary.rkt` with `write-u8/u16/u32/u64-le`, `read-u*-le`, `align-up`, `pad-to`, `compress-unsigned`, `compress-signed`, `decompress-unsigned`, `decompress-signed`.
* [ ] Replace `write-le-*`, `to-int`, `read-int`, `compressed` (writer), and `cli-decompress-unsigned` (reader) with the shared versions.
* [x] Fix the 2-byte compressed-integer limit (II.23.2, must be `#x3FFF`). The old `cli-compress-unsigned` is gone. The writer's `compressed` and the reader's `cli-decompress-unsigned` both use the correct bound. No boundary unit test exists yet.

### R2 One metadata schema

* [ ] Create `rangi/cli/schema.rkt` describing all 45 table ids (0x00-0x2C) as data: name, id, sorted key (if any), and columns. Column kinds: `u8`, `u16`, `u32`, `string`, `guid`, `blob`, `(index table)`, `(coded kind)`.
* [ ] Describe the 13 coded index kinds (II.24.2.6) as data: tag bits and the ordered table list, including unused tags in `CustomAttributeType`.
* [ ] Derive row sizes and coded index widths from the schema. Delete the two hand-written `case` blocks.
* [ ] Port `src/cli-reader.rkt` to `rangi/cli/reader.rkt` on top of the schema. Add a generic `(read-row rdr table rid)` that returns a vector, keeping the fast paths (`get-public-typedefs`) as specialised readers.
* [ ] Fix the remaining reader defects in [architecture.md](../architecture.md#reader): the `#-` stream and the extra-data flag. Already fixed in `ca7aa13`: PE32+, missing tables, `declsecurity` tag, visibility mask, and the port leak.

### R3 PE layer and layout engine

* [ ] `pe/model.rkt`: `image` (machine, characteristics, subsystem, dll flags, image base, alignments, PE32 or PE32+), `section` (name, characteristics, chunks), `chunk` (name, alignment, size, writer, symbols, fixups), `fixup` (offset, symbol, kind `rva32`/`va32`/`va64`/`file-offset`).
* [ ] `pe/layout.rkt`: assign RVAs (section alignment `0x2000`) and file offsets (file alignment `0x200`); compute all optional header size fields; return a layout plus the text map used by snapshot L2.
* [ ] `pe/write.rkt`: serialise the DOS stub, COFF header, optional header, data directories (by symbol), section table, and sections.
* [ ] `pe/imports.rkt`: build the import directory, ILT, IAT, hint/name entry for `_CorExeMain` or `_CorDllMain`, the `mscoree.dll` name, and the `FF 25` entry stub as chunks with fixups. The entry stub's absolute operand is a `va32` fixup.
* [ ] `pe/relocs.rkt`: generate `.reloc` blocks from all `va32`/`va64` fixups.
* [ ] `pe/read.rkt`: the header parsing currently inside `read-file`, shared with the reader.

### R4 CLI layer emits chunks

* [ ] `cli/heaps.rkt`: insertion-ordered heaps with dedup. The `#Strings` heap writes UTF-8; the `#US` heap writes a compressed length, UTF-16LE text, and the trailing flag byte (II.24.2.4); `#Blob`; `#GUID` (1-based index).
* [ ] `cli/tables.rkt`: rows are added through typed constructors and stored in insertion order. Sorted tables are sorted at serialisation time, with a remap of any tokens that point into them. Compute `Valid`, `Sorted`, `HeapSizes`, and row counts.
* [ ] `cli/metadata.rkt`: metadata root (signature, version string padded to 4, stream headers with computed offsets), as a single chunk.
* [ ] `cli/header.rkt`: CLI header with the entry point token from the model, flags (`ILONLY`, `32BITREQUIRED`, `32BITPREFERRED`, `STRONGNAMESIGNED`), and symbol fixups to the metadata and resources.
* [ ] Method bodies become one chunk each (4-byte aligned for fat headers), with `MethodDef.RVA` filled through a fixup.
* [ ] Delete every literal listed in [architecture.md](../architecture.md#writer).

### R5 Front end separation

* [ ] Move `parse-il` into `ilasm/syntax.rkt`, producing a plain module model (structs) with no heap or table knowledge.
* [ ] `image.rkt` glues `ilasm` -> `cli` -> `pe` and exposes `(write-image model path #:kind 'exe|'dll #:platform 'x86|'x64|'anycpu)`.
* [ ] Keep `src/cli-writer.rkt` and `src/cli-reader.rkt` as thin compatibility shims re-exporting the old names until experiments are migrated, then delete them.

### R6 Reader hardening

* [ ] Corpus test against every reference assembly (verification milestone V7).
* [ ] Benchmark `read-file` plus `get-public-typedefs` on `mscorlib.dll` and record the timing in a test, so phase-1 load time does not regress.
* [ ] Consider memory-mapping or reading only the metadata section instead of the whole file.
