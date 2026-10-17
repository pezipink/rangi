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
| P0    | this file                                               | Commit or shelve the current WIP; add `info.rkt`; move experiments out of `src/`        | `racket experiments/typed-il.rkt` still prints `203`                        |
| P1    | [verification.md](verification.md) V1-V3               | Characterisation snapshots of today's output; PEVerify, ildasm, and SRM dumps run       | `raco test tests/` green on the baseline image                              |
| P2    | [restructure.md](restructure.md) R1-R2                 | `private/binary.rkt` and `cli/schema.rkt` shared by reader and writer                    | Reader and writer produce identical bytes and parse results to P1 snapshots |
| P3    | [restructure.md](restructure.md) R3-R5                 | PE layer with a layout engine; CLI layer emits chunks; hardcodes removed                 | Layout map snapshot reviewed; PEVerify clean; `.text` larger than 0x400     |
| P4    | [opcodes.md](opcodes.md)                               | Full opcode table, labels, branch relaxation, fat bodies, EH                             | Opcode table matches the .NET oracle; IL fixtures pass ILVerify and run     |
| P5    | [cli-coverage.md](cli-coverage.md)                     | Fields, params, types, generics, attributes, DLLs, PE32+                                 | Each row in the coverage tracker has a passing fixture                      |
| P6    | [restructure.md](restructure.md) R6                    | Reader hardened against real assemblies (mscorlib, System.Private.CoreLib)               | Reader agrees with System.Reflection.Metadata on every reference assembly   |

P4 and P5 can interleave once P3 lands. P6 can start any time after P2, because the reader only depends on the shared schema.

## P0 checklist

* [ ] Decide what to do with the uncommitted changes to `src/cli-writer.rkt` and `src/cli-writer-test.rkt` (commit as WIP is the default).
* [ ] Add `info.rkt` declaring a `rangi` collection with `rackunit-lib` as a build dependency.
* [ ] Move `src/cli-writer-test.rkt` to `experiments/typed-il.rkt` and `src/cli-test.rkt` to `experiments/phase1-load.rkt`.
* [ ] Make the output path a parameter of `assemble` (default to a temp file) so tests and experiments stop sharing `c:\temp\rangi.exe`.
* [ ] Route debug output through a `rangi-log` logger instead of `writeln`.

## Open questions

* Target runtimes: .NET Framework only (mscoree `_CorExeMain`), or also .NET (Core) with a `runtimeconfig.json` and an apphost? This affects PE32+ priority and which reference assemblies fixtures use.
* Should the s-expression ilasm syntax stay close to textual ilasm (`.method`, `.class`), or move toward a Racket-native structure such as keyword arguments and structs?
* Is a PDB (portable PDB) needed for debugging generated code, and if so, in which phase?
* Is strong naming needed? It requires SHA-1 hashing of the image and an RSA signature, which is a significant feature.
