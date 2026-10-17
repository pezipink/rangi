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

Status: `src/private/binary.rkt` is the shared source for the little-endian, alignment, and compressed-integer helpers. The reader, writer, and PE layer use it, and `tests/binary-test.rkt` covers the boundaries. The signed compressed helpers (`compress-signed`, `decompress-signed`) are not implemented yet, because the II.23.2 signed encoding has not been verified against the spec and nothing calls them.

* [x] Create `rangi/private/binary.rkt` with `write-u8/u16/u32/u64-le`, `read-u*-le`, `align-up`, `pad-to`, `compress-unsigned`, and `decompress-unsigned`. (`compress-signed` and `decompress-signed` are deferred; see status above.)
* [x] Replace `write-le-*`, `to-int`, `read-int`, `compressed` (writer), and `cli-decompress-unsigned` (reader) with the shared versions.
* [x] Fix the 2-byte compressed-integer limit (II.23.2, must be `#x3FFF`). The old `cli-compress-unsigned` is gone. The writer's `compressed` and the reader's `cli-decompress-unsigned` both use the correct bound. `tests/binary-test.rkt` checks the 0x7F/0x80, 0x3FFF/0x4000, and 0x1FFFFFFF boundaries.

### R2 One metadata schema

* [x] Create `src/cli/schema.rkt` describing all 45 table ids (0x00-0x2C) as data: name, id, sorted key (if any), and columns. Column kinds: `u8`, `u16`, `u32`, `string`, `guid`, `blob`, `(index table)`, `(coded kind)`. Merged from `stream/a2`.
* [x] Describe the 13 coded index kinds (II.24.2.6) as data: tag bits and the ordered table list, including unused tags in `CustomAttributeType`.
* [x] Derive row sizes and coded index widths from the schema. Delete the two hand-written `case` blocks.
* [x] Port `src/cli-reader.rkt` onto the schema, in place. Add a generic `(read-row rdr table rid)` that returns a vector, keeping the fast paths (`get-public-typedefs`) as specialised readers. The reader moved to `src/cli/reader.rkt` in R5, with a shim left at `src/cli-reader.rkt`. `read-row` on mscorlib matches `get-public-typedefs` (1520 public types, same order).
* [x] Fix the remaining reader defects in [architecture.md](../architecture.md#reader): the `#-` stream and the extra-data flag. Already fixed in `ca7aa13`: PE32+, missing tables, `declsecurity` tag, visibility mask, and the port leak.

### R3 PE layer and layout engine

Deviations so far: a chunk holds plain bytes with zeroed holes and a list of typed `fixup` records (offset, kind, target chunk). The `digest` record fills the MVID from a SHA-256 over the other metadata streams once layout is known, which keeps existing MVIDs unchanged. `va32` is used for the PE32 entry stub and the `.reloc` table, and `va64` for the PE32+ stub. The image struct is named `image-params`, and the writer supports `'pe32` and `'pe32+`, selected by `(.format pe32+)`.

* [x] `pe/model.rkt`: `image-params` (format, machine, characteristics, subsystem, dll flags, image base, section and file alignment), `section`, `chunk`, `fixup` (kind `rva32`/`va32`/`va64`/`file-offset`), `digest`, `placement` (with `file-offset`), `placed-section`, and `placed-image`. `layout.rkt` re-exports these, so existing consumers do not change.
* [x] `pe/layout.rkt`: assign RVAs (section alignment `0x2000`) and file offsets (file alignment `0x200`); compute all optional header size fields (the fixed header size depends on the format); return a layout plus the text map used by snapshot L2. The layout map is `layout-report`, snapshotted as `layout.txt` (V5). Each fixup kind has its own width (`rva32`/`va32`/`file-offset` are 4 bytes, `va64` is 8).
* [x] `pe/write.rkt`: serialise the DOS stub, COFF header, optional header, data directories (by symbol), section table, and sections. The COFF and optional header values come from `image-params`.
* [x] `pe/imports.rkt`: build the import directory, ILT, IAT, hint/name entry for `_CorExeMain` or `_CorDllMain`, the `mscoree.dll` name, and the entry stub as chunks with fixups. The PE32 stub is `FF 25 <abs32>` with a `va32` operand fixup. The PE32+ stub is `movabs rax, [abs64]; jmp rax` with a `va64` operand fixup, because `FF 25` cannot reach a 64-bit IAT. Built for `_CorExeMain` only, with no DLL variant.
* [x] `pe/relocs.rkt`: generate `.reloc` blocks from `va32` (HIGHLOW) and `va64` (DIR64) fixups.
* [x] `pe/read.rkt`: `read-pe-headers` parses the DOS, PE, optional, and section headers, and `rva->file-offset` maps an RVA through them. `cli-reader.rkt` uses both. `tests/pe-read-test.rkt` checks the round trip against the writer's placements.

### R4 CLI layer emits chunks

* [x] `cli/heaps.rkt`: insertion-ordered heaps with dedup. The `#Strings` heap writes UTF-8; the `#US` heap writes a compressed length, UTF-16LE text, and the trailing flag byte (II.24.2.4); `#Blob`; `#GUID` (1-based index). Merged from `stream/c-heaps`; the writer does not use it yet.
* [x] `cli/tables.rkt`: rows are added with `add-row!`, which takes the table name and the columns in schema order, and checks arity and ranges against `schema.rkt`. Deviation: one generic constructor instead of per-table constructors, because the schema is already the single source of row layouts. Rows are stored in insertion order. `sort-tables!` sorts the sorted tables in dependency order, remaps every index and coded index into them, and errors on a cycle. `tables-stream` computes `Valid`, `Sorted`, `HeapSizes`, and row counts, and returns the MethodDef RVA fixups. Covered by `tests/cli/tables-test.rkt`.
* [x] `cli/metadata.rkt`: metadata root (BSJB, version `v4.0.30319` padded to 4, stream headers with computed offsets), as a single chunk. The MVID is a digest over the other streams, written into `#GUID` at layout.
* [x] `cli/header.rkt`: CLI header chunk (II.25.3.3) with the entry token from the model and a fixup to the metadata chunk. Flags default to `ILONLY`. Deviation: `32BITREQUIRED`, `32BITPREFERRED`, and `STRONGNAMESIGNED` are not set yet, because nothing needs them. Resources are not emitted.
* [x] Method bodies are one chunk each, 4-byte aligned. The MethodDef RVA is written as an `rva-ref` cell, and `tables-stream` returns it as a fixup, so the writer no longer patches offsets by hand. Bodies were already chunks before R4.
* [ ] Delete every literal listed in [architecture.md](../architecture.md#writer). Partly done: the hand-written row layouts and the CLI header and metadata literals are gone. Still open: opcode bytes in `encode-il` in `cli/lower.rkt` (O4 replaces them), and the PE machine, flag, and section constants in `image.rkt` (the PE layer).


### R5 Front end separation

* [x] Move `parse-il` into `ilasm/syntax.rkt`, producing a plain module model (structs) with no heap or table knowledge. Also `lower.rkt` (model to `cli-program`, interning and IL bytes) and `cli/build.rkt` (metadata chunk). Verified by `nano` (42, 84) and an unchanged suite with no snapshot or hash changes.
* [x] `image.rkt` glues `ilasm` -> `cli` -> `pe` and exposes `write-image`, `assemble`, and `image-layout-report`. Deviation: the signature is `(write-image model path)`, without `#:kind` or `#:platform`. There is no DLL output and no x86 or anycpu support yet (`pe/imports.rkt` only imports `_CorExeMain`), so those keywords are deferred until something needs them.
* [x] `src/cli-writer.rkt` deleted, since its callers now use `ilasm/syntax.rkt` and `image.rkt` directly. `src/cli-reader.rkt` is a re-export shim of `src/cli/reader.rkt` (moved with `git mv`). Delete the shim once the reader callers are migrated.


### R6 Reader hardening

* [x] Corpus test against every reference assembly (verification milestone V7).
* [x] Benchmark `read-file` plus `get-public-typedefs` on `mscorlib.dll` and record the timing in a test. Timings are recorded, not asserted, so this does not yet guard against a load-time regression.
* [ ] Consider memory-mapping or reading only the metadata section instead of the whole file.
