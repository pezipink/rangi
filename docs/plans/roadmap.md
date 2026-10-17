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

Last updated after the Wave 1 lane merges (PE constants, FieldSig and flags, `ldstr`/`switch` fixtures, `filter` EH and prefix validation). `RANGI_REQUIRE_ORACLES=1 raco test -j 4 tests/` passes (1086 tests at `3223340`, about 53 s). Start here, then read [AGENTS.md](../../AGENTS.md), [architecture.md](../architecture.md), and [workflow.md](workflow.md) before you run lanes.

Done:

* P0 cleanup, and P1 harness (V1 to V3). `racket experiments/nano.rkt` prints `42` and `84`.
* V0 determinism: insertion-ordered rows and heaps, content-hash MVID, COFF timestamp 0.
* V4 L5 structural lint (`tests/lib/pe-lint.rkt`, tested by `tests/image-lint-test.rkt`).
* Writer rewrite: `<Module>` methods move to a generated `Program` class; `.entrypoint` sets the entry token; unknown IL raises.
* Reader defects R1 to R10 fixed. PE32 and PE32+ nano dumps match System.Reflection.Metadata. The mscorlib public type count matches the SRM oracle (1520; the earlier 1521 figure was wrong, see `tests/read-bench-test.rkt`). Stream D baseline: lazy open median about 6.5 ms, enumerate public types median about 0.5 ms (20 runs, 4.7.1 mscorlib).
* P3 bigger fixtures: `tests/fixtures/text-over-400` (`.text` VirtualSize 0x476) and `tests/fixtures/text-over-2000` (0x2346). Both pass PEVerify, ildasm, SRM, and the lint. `fixtures-test.rkt` asserts the 0x400 and 0x2000 limits. The O4 short-form `ldc.i4` change had shrunk them, so they were grown back. The layout map (V5) is in place.
* O4 method bodies merged: `.locals`, computed maxstack, catch, finally, fault, and `filter` EH, plus prefix validation, and the `ops-*` opcode batch fixtures (PEVerify and ILVerify clean).
* `ldstr-hello` (UTF-16 `#US` text, including non-ASCII) and `switch-dispatch` execution fixtures merged.
* FieldSig (0x06) codec with custom mods, and FieldAttributes and ParamAttributes constants in `src/cli/flags.rkt`. Unit-tested only; not wired into ilasm syntax yet.
* PE header, section, and directory constants are named in `src/pe/constants.rkt`. Output is byte-identical.
* Same-module calls merged (`calls-multi`): forward calls and recursion. The writer gap where `call` only accepted MemberRef is closed.
* Generics merged: data layer, signatures, reader, ilasm syntax, and generic same-module calls (`generic-calls`).
* Arrays merged (`arrays-sum`): `newarr`, `ldelem`, `stelem`, `ldlen`, `ldelema`, and `szarray` types.
* V7 reader corpus test and the metadata dump decode MethodSpec. mscorlib's 656 MethodSpec rows match SRM.

Open items, in order:

1. Done: the reader accepts the `#-` uncompressed stream and the HeapSizes extra-data bit (0x40), and skips unknown streams such as `#!`. The 6th-edition text does not define `#-` or 0x40, so this follows SRM (see [verification.md](verification.md#spec-sources-and-discovery)). `tests/stream-variants-test.rkt` patches nano into a `#-`/0x40 image and a `#!` variant. The patcher handles PE32 images only; PE32+ is not covered.
2. Done: `tests/lib/metadata-dump.rkt` decodes every II.22 table except the pointer and edit-and-continue tables, which it rejects when they hold rows. SRM dumps the same rows.
3. Done: V7 reader corpus test over the .NET 4.7.1 reference assemblies and `System.Private.CoreLib`, diffed against SRM. 133 of 133 assemblies match.
4. Done: P2 R1 and R2 (A1 and A2 merged). `src/private/binary.rkt` holds the little-endian, compressed-integer, alignment, and pad-to helpers. `src/cli/schema.rkt` is the single source of table and coded-index layouts, and the reader and writer both use it. Signed compressed integers are still open; nothing calls them. `src/cli/heaps.rkt` is merged (C), and the writer uses it.
5. Done: V5 L2 layout map, landed with R3.
6. Partly done: V6 ilasm differential fixtures. `ldstr-hello` and `switch-dispatch` are in. The rest wait for P5 features.
7. Writer gaps: follow the "Suggested order" in [cli-coverage.md](cli-coverage.md).
8. Done: the ILVerify oracle (L6) is in `tests/oracles/ilverify`, checked by `tests/oracles/ilverify-test.rkt`.

## Phase status

| Phase | Status | What remains |
|-------|--------|--------------|
| P0 | Done | None |
| P1 | Done | None |
| P2 | Done | R1 and R2 merged. Signed compressed integers are deferred until a caller needs them |
| P3 | Done | R3, V5, R4, and R5 are done. The threshold fixtures pass the 0x400 and 0x2000 limits (0x476 and 0x2346), and a person reviewed the layout snapshots. PE constants are named. Still open: the DOS stub blob and the CLI-side literals in `encode-il`. |
| P4 | Done | O1 to O5 are merged, including `filter` EH, prefix validation, and the `il-all-opcodes` fixture. Its stdout is checked, and PEVerify and ILVerify pass. Unverifiable opcodes are in `il-unverifiable-opcodes`, and TypedReference and calli are in `il-runtime-only-opcodes`. |
| P5 | Partly done | Done: generic methods and types (signatures, TypeSpec, MethodSpec, GenericParam), same-module calls, same-module static fields, instance methods, `.ctor`, `newobj`, single-dimension arrays, catch, finally, and fault EH. External instance calls via the `instance` keyword are done (`instance-external-call`). Multiple types with namespaces and class-typed members are done (`multi-types`), and so is `extends` to a same-module or external base (`extends-base`). Open: value types and enums, interfaces, attributes, and DLLs (see [cli-coverage.md](cli-coverage.md)). |
| P6 | Mostly done | V7 corpus diff matches SRM on 133 of 133 assemblies. The benchmark and memory-mapping items in R6 are open. |

## Next steps

The remaining critical path is P5: multiple types, interfaces, value types, attributes, and DLLs. Each step keeps `RANGI_REQUIRE_ORACLES=1 raco test tests/` green.

1. Done: P2, part A1 (R1). Helpers live in `src/private/binary.rkt`, and the reader and writer use them. Merged from `stream/a1`.
2. Done: P2, part A2 (R2), merged from `stream/a2`.
3. Done: R4 (CLI emits chunks). Heaps, tables, metadata root, CLI header, and body chunks.
4. Done: R5 (front-end split). `parse-il` is in `ilasm/syntax.rkt`, lowering is in `cli/lower.rkt`, the metadata chunk is in `cli/build.rkt`, and `image.rkt` writes the image. `cli-writer.rkt` is deleted. The reader moved to `cli/reader.rkt`, with a shim at `cli-reader.rkt` until its callers are migrated.
5. Done: P3 closed after the threshold fixtures were grown and a person reviewed the layout snapshots.
6. P4 and P5 remaining work is listed in the phase table and in [opcodes.md](opcodes.md) and [cli-coverage.md](cli-coverage.md). The operand encoders, labels, and relaxation are wired to the writer.

## What can run in parallel

Each stream owns files that no other stream touches, so the streams can run in separate git worktrees. Merge each with `git merge --no-ff`, as the last batch did.

| Stream | Work | Owns | Start |
|--------|------|------|-------|
| A | P2 and R4/R5 | Done (merged). | None. |
| B | O2 operand encoders and O3 labels and branch relaxation | `src/il/encode.rkt`, `src/il/labels.rkt`, `tests/il/` | Done (merged) and wired to the writer. |
| C | R4 heaps | `src/cli/heaps.rkt`, `tests/cli/heaps-test.rkt` | Done (merged). |
| D | R6 benchmark: timing of `read-file` plus `get-public-typedefs` on mscorlib | `tests/read-bench-test.rkt` | Done (merged). Timings recorded, not asserted. |
| E | Decode signatures and heap entries in the L3 dump | `tests/lib/metadata-dump.rkt` | Done (merged). |
| F | O4 method bodies and opcode batches | `src/il/`, `src/cli/lower.rkt`, `src/il/stack.rkt`, `tests/fixtures/ops-*` | Done (merged to `main`). `filter` EH, prefix validation, and `il-all-opcodes` are in. |
| I | Wave 1: PE constants, FieldSig and flags, `ldstr`/`switch` fixtures, `filter` EH | `src/pe/constants.rkt`, `src/cli/flags.rkt`, `tests/fixtures/ldstr-hello`, `tests/fixtures/switch-dispatch`, `tests/fixtures/ops-eh-filter` | Done (merged to `main`). Four lanes ran in parallel, about 10 min wall time. |
| G | Generics: data layer, signatures, reader, ilasm syntax, generic calls | `src/cli/sigs.rkt`, `src/cli/reader.rkt`, `src/ilasm/syntax.rkt`, `tests/fixtures/generic-calls` | Done (merged to `main`). |
| H | Same-module calls, finally and fault EH, single-dimension arrays | `src/cli/lower.rkt`, `tests/fixtures/calls-multi`, `tests/fixtures/arrays-sum`, `tests/fixtures/ops-eh-finally` | Done (merged to `main`). |

Not parallel:

* Lanes that touch `cli/lower.rkt` still conflict with one another. The generic-calls lane needed a manual merge of 10 hunks. Keep one lane per file at a time.
* V6 ilasm differential fixtures for unsupported features. They can't pass until those features exist. Start them alongside P5, not before.

Expected gain: the next gains are the P4 open items, then P5 instance members and types.


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
