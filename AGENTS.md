---
title: Rangi agent guide
description: Always-on context for AI agents working in the Rangi Racket CLI/PE toolbox
---

## What Rangi is

Rangi is a Racket toolbox for building .NET languages. It has two halves:

* A fast, lazy reader for CLI (ECMA-335) metadata in `.exe`/`.dll` files, meant to run at Racket phase 1 (macro expansion time) so compilers can see referenced assemblies' types.
* An ilasm-like s-expression assembler that writes runnable Windows PE/CLI images.

The code is an early, exploratory prototype. Read [docs/architecture.md](docs/architecture.md) before changing anything. It describes the current files, the known bugs and hardcoded values, and the target layering.

## Plans

Work is driven by the plans in [docs/plans/](docs/plans/). Start with [roadmap.md](docs/plans/roadmap.md), which orders the phases. Each plan has a checklist; tick items as you complete them and keep the plans current.

| Plan                                                      | Covers                                                        |
|-----------------------------------------------------------|---------------------------------------------------------------|
| [roadmap.md](docs/plans/roadmap.md)                       | Phase order, gates between phases, open questions             |
| [verification.md](docs/plans/verification.md)             | How images and layout are verified (do this first)            |
| [restructure.md](docs/plans/restructure.md)               | Splitting PE image writing from CLI metadata, module layout   |
| [opcodes.md](docs/plans/opcodes.md)                       | Full ECMA-335 Partition III opcode table and IL assembler     |
| [cli-coverage.md](docs/plans/cli-coverage.md)             | Spec coverage tracker: tables, signatures, bodies, PE features |

## Ground rules

* Keep the raw PE image layer free of CLI knowledge. The PE layer lays out sections and resolves RVAs; the CLI layer produces metadata, IL, and the CLI header as byte chunks with symbolic fixups. See [restructure.md](docs/plans/restructure.md).
* Keep one source of truth for metadata table schemas, coded indexes, and opcodes. Both the reader and the writer must consume the same data tables; never hand-copy row layouts again.
* Output must be deterministic. Never iterate a mutable `hash` to decide row order, heap order, or layout. Use insertion-ordered structures or explicit sorts. Timestamps and MVIDs come from inputs or content hashes, not the clock.
* The reader stays lazy and fast. The macro expander calls it repeatedly at phase 1, so decode rows on demand. `read-file` must not cache; each call reads the file. Add eager work or caching only with a benchmark.
* Every change to emitted bytes must be visible in a reviewed snapshot (layout map, metadata dump, image hash). If a snapshot changes, explain why in the commit.
* Cite the ECMA-335 section (for example `II.22.37`, `II.25.3.3`, `III.3.4`) in comments where code encodes spec rules.
* Where the ECMA-335 6th edition is silent (`#-`, HeapSizes 0x40), follow System.Reflection.Metadata in dotnet/runtime, not web search summaries. Record findings in [verification.md](docs/plans/verification.md#spec-sources-and-discovery).
* Do not write outside the repo or the system temp directory. Generated images go under `build/` or a temp directory, never `c:\temp` hardcoded.

## Build and test

Racket 8.16 CS is installed at `C:\Program Files\Racket`. Run the test suite with:

```powershell
raco test tests/
```

It runs the fixture checks (image hash, stdout, exit code) and the external oracles. Oracles are skipped when their tool is missing. It also runs the structural lint (`tests/lib/pe-lint.rkt`, tested by `tests/image-lint-test.rkt`) on every fixture. The metadata dump decodes MethodSpec rows (they match SRM on mscorlib), and it decodes every II.22 table except the pointer and edit-and-continue tables, which it rejects when they hold rows. The V7 corpus test diffs 133 reference assemblies against SRM (see [verification.md](docs/plans/verification.md)). `RANGI_UPDATE_SNAPSHOTS=1 raco test tests/` rewrites reviewed snapshots; only do that when the change to emitted bytes is intended and explained in the commit.

The smoke test is still:

```powershell
racket experiments/nano.rkt   # assembles nano and nano2 into the temp dir, runs them; prints 42 and 84
```

Library code logs debug and warning output through the `rangi` logger (`src/log.rkt`), so it is silent by default. To see it on stderr, set `PLTSTDERR="warning@rangi"` (or `debug@rangi`).

External oracles available on this machine:

* `PEVerify.exe` and `ildasm.exe` under `C:\Program Files (x86)\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\`
* `ilasm.exe` under `C:\Windows\Microsoft.NET\Framework\v4.0.30319\`
* .NET SDKs 9 and 10 (`dotnet`), for System.Reflection.Metadata and ILVerify based checks
* Reference assemblies under `C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.7.1\`

## Repo quirks

* The repo directory is owned by a different Windows user. `C:/repos/rangi` is in the global `safe.directory` list, so plain `git` commands work.
* `$env:TEMP` can be an 8.3 short path that Racket cannot open. When you pass a temp path to Racket from PowerShell, use the long path form.
* `*.bak` and `compiled/` are gitignored scratch files from DrRacket. Ignore them.
* Racket files use `#lang racket` or `#lang racket/base`. Prefer `racket/base` plus explicit requires for library modules (the reader must load fast at phase 1).
