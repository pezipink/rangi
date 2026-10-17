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
| P3    | [restructure.md](restructure.md) R3-R5                 | PE layer with a layout engine; CLI layer emits chunks; hardcodes removed                 | Layout map snapshot reviewed; PEVerify clean; `.text` larger than 0x400     |
| P4    | [opcodes.md](opcodes.md)                               | Full opcode table, labels, branch relaxation, fat bodies, EH                             | Opcode table matches the .NET oracle; IL fixtures pass ILVerify and run     |
| P5    | [cli-coverage.md](cli-coverage.md)                     | Fields, params, types, generics, attributes, DLLs                                        | Each row in the coverage tracker has a passing fixture                      |
| P6    | [restructure.md](restructure.md) R6                    | Reader hardened against real assemblies (mscorlib, System.Private.CoreLib)               | Reader agrees with System.Reflection.Metadata on every reference assembly   |

P4 and P5 can interleave once P3 lands. P6 can start any time after P2, because the reader only depends on the shared schema.

## Status

Last updated at commit `ca7aa13`. Start here, then read [AGENTS.md](../../AGENTS.md) and [architecture.md](../architecture.md).

Done:

* P0 cleanup, and P1 harness (V1 to V3). `raco test tests/` passes (10 tests). `racket experiments/nano.rkt` prints `42` and `84`.
* V0 determinism: insertion-ordered rows and heaps, content-hash MVID, COFF timestamp 0.
* V4 L5 structural lint (`tests/lib/pe-lint.rkt`, tested by `tests/image-lint-test.rkt`).
* Writer rewrite: `<Module>` methods move to a generated `Program` class; `.entrypoint` sets the entry token; unknown IL raises; supported IL is `ret`, `add`, `ldc.i4`, and `call`.
* Reader defects R1 to R10 fixed, except the two open items below. PE32 and PE32+ nano dumps match System.Reflection.Metadata. The mscorlib public type count matches (1521).
* The P3 gate ".text larger than 0x400" still needs a fixture. The writer uses 0x200 file alignment and 0x2000 section alignment, but no fixture covers a `.text` over 0x400 yet.

Open items, in order:

1. Reader: accept the `#-` uncompressed stream and the HeapSizes extra-data bit (0x40), and skip unknown streams such as `#!` instead of rejecting them. The 6th-edition text does not define `#-` or 0x40, so follow SRM (see [verification.md](verification.md#spec-sources-and-discovery)). Unblocked; not started.
2. Done: `tests/lib/metadata-dump.rkt` decodes MethodSpec rows, and the SRM oracle dumps them. mscorlib's 656 MethodSpec rows match SRM exactly. mscorlib is still compared by public type count, because the decoder does not yet cover TypeSpec, CustomAttribute, and other tables. That gap belongs to item 3.
3. V7 reader corpus test over the .NET 4.7.1 reference assemblies and `System.Private.CoreLib`, diffed against SRM.
4. P2 (R1, R2): `rangi/private/binary.rkt` and `rangi/cli/schema.rkt`. The reader and writer still hand-copy their layouts. Boundary values `0x3FFF` and `0x4000` for compressed integers have no unit test yet.
5. V5 L2 layout map, landing with R3.
6. V6 ilasm differential fixtures. Start with the `ldstr` hello world: it needs `#US` content, which the writer does not produce yet.
7. Writer gaps: follow the "Suggested order" in [cli-coverage.md](cli-coverage.md).
8. The ILVerify oracle (L6) is not implemented. `tests/oracles/ilverify` does not exist.
## Handoff

* Start with item 1. Its spec question is answered by SRM, not the ECMA text. The corpus scan found no `#-` sample locally, so build a test image by patching a `#~` image: rename the stream to `#-` and set 0x40 with 4 extra bytes. Compare the dump with SRM.
* Add a unit test that the reader skips `#!` (NGEN images), and cite SRM's `default: continue` in the code comment.
* Item 3 needs TypeSpec, CustomAttribute, and GenericParam decoding in `tests/lib/metadata-dump.rkt` before mscorlib can be compared fully.

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

Consequence: fixtures are PE32 only. The PE32+ reader fix landed in `ca7aa13` and is checked against `ilasm /X64` images. The PE32+ writer stays out of scope for Framework fixtures.
