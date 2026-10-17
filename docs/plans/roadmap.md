---
title: Rangi roadmap
description: Ordered phases for cleaning up Rangi, with gates between phases and open questions
ms.date: 2026-10-17
---

## Principles

* Build the safety net before moving code. Every phase after V1 is gated by the verification harness.
* Refactor without changing bytes first, then fix bugs and remove hardcodes with snapshot diffs that explain each change.
* Grow spec coverage behind fixtures: a feature is done when it has a fixture that passes every oracle in [verification.md](verification.md).

## Phases

| Phase | Plan                                                    | Outcome                                                                                 | Gate to leave the phase                                                    |
|-------|---------------------------------------------------------|-----------------------------------------------------------------------------------------|-----------------------------------------------------------------------------|
| P0    | this file                                               | Shelve the WIP (done: `stash@{0}`); add `info.rkt`; move experiments out of `src/`; route output through a logger; parameterise the output path | `racket experiments/nano.rkt` prints `42` and `84`, and the image hash matches `tests/fixtures/nano/image.sha256` (the baseline was re-pinned on purpose in `ca7aa13`: `Program` class and deterministic MVID) |
| P1    | [verification.md](verification.md) V1-V3               | Characterisation snapshots of today's output; PEVerify, ildasm, and SRM dumps run       | `raco test tests/` green on the baseline image                              |
| P2    | [restructure.md](restructure.md) R1-R2                 | `private/binary.rkt` and `cli/schema.rkt` shared by reader and writer                    | Reader and writer produce identical bytes and parse results to P1 snapshots |
| P3    | [restructure.md](restructure.md) R3-R5                 | PE layer with a layout engine; CLI layer emits chunks; hardcodes removed                 | Layout map snapshot reviewed; PEVerify clean; `.text` larger than 0x400 and 0x2000 |
| P4    | [opcodes.md](opcodes.md)                               | Full opcode table, labels, branch relaxation, fat bodies, EH                             | Opcode table matches the .NET oracle; IL fixtures pass ILVerify and run     |
| P5    | [cli-coverage.md](cli-coverage.md)                     | Fields, params, types, generics, attributes, DLLs                                        | Each row in the coverage tracker has a passing fixture                      |
| P6    | [restructure.md](restructure.md) R6                    | Reader hardened against real assemblies (mscorlib, System.Private.CoreLib)               | Reader agrees with System.Reflection.Metadata on every reference assembly   |

P4 and P5 can interleave once P3 lands. P6 can start any time after P2, because the reader only depends on the shared schema.

## Status

Last updated after the A2, B+ (O5 tests), and C (heaps) merges (October 17, 2026). `raco test tests/` passes (865 tests). Start here, then read [AGENTS.md](../../AGENTS.md) and [architecture.md](../architecture.md).

Done:

* P0 cleanup, and P1 harness (V1 to V3). `raco test tests/` passes (33 tests, with `RANGI_REQUIRE_ORACLES=1`). `racket experiments/nano.rkt` prints `42` and `84`.
* V0 determinism: insertion-ordered rows and heaps, content-hash MVID, COFF timestamp 0.
* V4 L5 structural lint (`tests/lib/pe-lint.rkt`, tested by `tests/image-lint-test.rkt`).
* Writer rewrite: `<Module>` methods move to a generated `Program` class; `.entrypoint` sets the entry token; unknown IL raises; supported IL is `ret`, `add`, `ldc.i4`, and `call`.
* Reader defects R1 to R10 fixed, except the two open items below. PE32 and PE32+ nano dumps match System.Reflection.Metadata. The mscorlib public type count matches the SRM oracle (1520; the earlier 1521 figure was wrong, see `tests/read-bench-test.rkt`). Stream D baseline: lazy open median about 6.5 ms, enumerate public types median about 0.5 ms (20 runs, 4.7.1 mscorlib).
* P3 bigger fixtures: `tests/fixtures/text-over-400` (`.text` VirtualSize 0x48E, 2 classes and 4 methods) and `tests/fixtures/text-over-2000` (`.text` 0x21A2, 8 classes and 64 methods). Both have fat IL bodies (code over 64 bytes, and `.maxstack 9` on some methods), and both pass PEVerify, ildasm, SRM, and the lint. `fixtures-test.rkt` asserts each `.text` stays above its threshold. The layout map (V5) is now in place.
* Known writer gap: `call` only accepts MemberRef, so the non-entry methods in the bigger fixtures are never executed. They are checked by the oracles and lint only.

Open items, in order:

1. Done: the reader accepts the `#-` uncompressed stream and the HeapSizes extra-data bit (0x40), and skips unknown streams such as `#!`. The 6th-edition text does not define `#-` or 0x40, so this follows SRM (see [verification.md](verification.md#spec-sources-and-discovery)). `tests/stream-variants-test.rkt` patches nano into a `#-`/0x40 image and a `#!` variant. Both run, and their dumps match the `#~` dump and SRM. The patcher handles PE32 images only; PE32+ is not covered.
2. Done: `tests/lib/metadata-dump.rkt` decodes MethodSpec rows, and the SRM oracle dumps them. mscorlib's 656 MethodSpec rows match SRM exactly. Item 3 completed the decoder for all II.22 tables.
3. Done: V7 reader corpus test over the .NET 4.7.1 reference assemblies and `System.Private.CoreLib`, diffed against SRM. 133 of 133 assemblies match.
4. Done: P2 R1 and R2 (A1 and A2 merged). `src/private/binary.rkt` holds the little-endian, compressed-integer, alignment, and pad-to helpers. `src/cli/schema.rkt` is the single source of table and coded-index layouts, and the reader and writer both use it. Signed compressed integers are still open; nothing calls them. `src/cli/heaps.rkt` is merged (C), but the writer does not use it yet.
5. Done: V5 L2 layout map, landed with R3.
6. Not started: V6 ilasm differential fixtures. Start with the `ldstr` hello world, which needs `#US` content that the writer does not produce yet (R4 heaps).
7. Writer gaps: follow the "Suggested order" in [cli-coverage.md](cli-coverage.md).
8. Done: the ILVerify oracle (L6) is in `tests/oracles/ilverify`, checked by `tests/oracles/ilverify-test.rkt`.

## Phase status (October 17, 2026)

| Phase | Status | What remains |
|-------|--------|--------------|
| P0 | Done | None |
| P1 | Done | None |
| P2 | Done | R1 and R2 merged. Signed compressed integers are deferred until a caller needs them |
| P3 | Partly done | R3, V5, R4, and R5 are done. The partial literal removal in R4 stays open until O4 and the PE constants move. Close P3 after a person reviews the layout snapshots. |
| P4 | Started | O1, O2, and O3 done (B merged). O5 unit and relaxation tests merged. O4 and the rest of O5 are open. O4 method bodies depend on R4. |
| P5 | Not started | Depends on R4 and R5 (both done). Now unblocked. |
| P6 | Mostly done | V7 corpus diff matches SRM on 133 of 133 assemblies. The benchmark and memory-mapping items in R6 are open. |

## Next steps

The critical path is P2, then R4, then R5, then closing P3, then P4 integration. Each step keeps `raco test tests/` green.

1. Done: P2, part A1 (R1). Helpers live in `src/private/binary.rkt`, and the reader and writer use them. Signed compressed integers are still open. Merged from `stream/a1`.
2. Done: P2, part A2 (R2), merged from `stream/a2`.
3. Done: R4 (CLI emits chunks). Heaps, tables, metadata root, CLI header, and body chunks. The literal removal is partly done, and the opcode and PE constants stay until O4 and the PE layer.
4. Done: R5 (front-end split). `parse-il` is in `ilasm/syntax.rkt`, lowering is in `cli/lower.rkt`, the metadata chunk is in `cli/build.rkt`, and `image.rkt` writes the image. `cli-writer.rkt` is deleted. The reader moved to `cli/reader.rkt`, with a shim at `cli-reader.rkt` until its callers are migrated.
5. Close P3 once the layout snapshots have been reviewed by a person.
6. P4 (O2 to O5). Operand encoders, labels, and relaxation go in as pure modules and are wired to the writer at O4.

## What can run in parallel

Each stream owns files that no other stream touches, so the streams can run in separate git worktrees. Merge each with `git merge --no-ff`, as the last batch did.

| Stream | Work | Owns | Start |
|--------|------|------|-------|
| A | P2 and R4/R5 | Done (merged). | None. |
| B | O2 operand encoders and O3 labels and branch relaxation | `src/il/encode.rkt`, `src/il/labels.rkt`, `tests/il/` | Done (merged). Wire in at O4. |
| C | R4 heaps | `src/cli/heaps.rkt`, `tests/cli/heaps-test.rkt` | Done (merged). |
| D | R6 benchmark: timing of `read-file` plus `get-public-typedefs` on mscorlib | `tests/read-bench-test.rkt` | Done (merged). Timings recorded, not asserted. |
| E | Decode signatures and heap entries in the L3 dump (not checked yet) | `tests/lib/metadata-dump.rkt` | Unblocked by A2 (merged). Can start now. |
| F | O4 pure encoders (opcode table and byte encoding) | `src/il/` | Partly done (stream/o4). Wired into lowering with `.locals`, maxstack analysis, and opcode batch fixtures (ILVerify and PEVerify clean). Catch-only EH; finally, fault, filter, prefix validation, operand syntax, and the all-opcodes fixture are open. Not merged to main. |

Not parallel:

* O4 (method bodies, locals, exception handling). Its body chunks exist now, so it is unblocked, but it changes `cli/lower.rkt` `encode-il`, so it should not run alongside other edits to that file.
* Writer features in P5. They depend on R4 and R5, which are both done.
* V6 ilasm differential fixtures for unsupported features. They can't pass until those features exist. Start them alongside P5, not before.

Expected gain: the critical path is now closed through R5. The next critical path is P4 (O4) and then P5. E and F can run in parallel with P4 work.

## Handoff

* Item 1 is done. The `#-` and `#!` checks come from patched nano images (`tests/lib/patch-image.rkt`), not a unit test of the reader alone. The 0x40 field is read and discarded, as in SRM, and the stream-name rule cites SRM's `default: continue`.
* Item 3 is done. `tests/lib/metadata-dump.rkt` decodes all II.22 tables, and the corpus diff runs against SRM.

## P0 checklist

* [x] Shelve the uncommitted changes to `src/cli-writer.rkt` and `src/cli-writer-test.rkt` in `stash@{0}` ("typed-expr experiment and debug edits"). Restore with `git stash pop` when the experiment is needed. Its test file moved, so pop it into `experiments/typed-il.rkt` and fix the paths.
* [x] Add `info.rkt` declaring a `rangi` collection with `rackunit-lib` as a build dependency.
* [x] Move `src/cli-writer-test.rkt` to `experiments/nano.rkt` and `src/cli-test.rkt` to `experiments/phase1-load.rkt`. The committed test prints `42` and `84`, not `203`; the `203` figure came from the WIP experiment.
* [x] Make the output path a parameter of `assemble` (default to a temp file) so tests and experiments stop sharing `c:\temp\rangi.exe`.
* [x] Route debug output through a `rangi` logger (`src/log.rkt`) instead of `writeln`. Remove the module-level `nano2` run from the library.

## Decisions

Decided by the user (October 2026). Plans must follow these unless the user changes them.

* **Target runtime: .NET Framework only.** Entry is `_CorExeMain` through mscoree, and fixtures run on the Framework 4.x reference assemblies. .NET (Core) targets, `runtimeconfig.json`, and apphost are out of scope for now.
* **Syntax: stay close to textual ilasm.** Keep `.method`, `.class`, and keyword lists such as `(public static)`. Do not move to a Racket-native structure.
* **No portable PDB yet.** The debug directory and PDB are out of scope until the user asks for them.
* **No strong naming.** The strong-name signature and `STRONGNAMESIGNED` flag stay out of scope.
* **Assembly name is the output file's basename.**
* **`main` moves off `<Module>`.** Methods declared on `<Module>` go into a generated `Program` class, because the CLR rejects entry points on `<Module>` (PEVerify `0x8013129d`).
* **Rows and heaps keep insertion order.** Output never depends on hash iteration.
* **MVID is a content hash, and the COFF timestamp is 0.** There is no timestamp option.
* **Fix every writer and reader bug, not a subset.** Unknown IL nodes raise an error. They are never skipped.
* **The reader stays lazy and fast.** The macro expander calls it repeatedly at phase 1. Decode rows on demand. `read-file` must not cache: each call reads the file. Add eager work or caches only with a benchmark.

Consequence: most fixtures are PE32. `nano-x64` is the one PE32+ writer fixture. The PE32+ reader fix landed in `ca7aa13` and is checked against `ilasm /X64` images. ARM64 stays out of scope.
