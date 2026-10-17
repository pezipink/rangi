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
* Every change to emitted bytes must be visible in a reviewed snapshot (layout map, metadata dump, image hash). If a snapshot changes, explain why in the commit.
* Cite the ECMA-335 section (for example `II.22.37`, `II.25.3.3`, `III.3.4`) in comments where code encodes spec rules.
* Do not write outside the repo or the system temp directory. Generated images go under `build/` or a temp directory, never `c:\temp` hardcoded.

## Build and test

Racket 8.16 CS is installed at `C:\Program Files\Racket`. Today there is no package or test suite. The current smoke test is:

```powershell
cd src
racket cli-writer-test.rkt   # writes c:\temp\rangi.exe and runs it; prints 203
```

Once [verification.md](docs/plans/verification.md) phase V1 lands, use `raco test tests/` instead.

External oracles available on this machine:

* `PEVerify.exe` and `ildasm.exe` under `C:\Program Files (x86)\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\`
* `ilasm.exe` under `C:\Windows\Microsoft.NET\Framework\v4.0.30319\`
* .NET SDKs 9 and 10 (`dotnet`), for System.Reflection.Metadata and ILVerify based checks
* Reference assemblies under `C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.7.1\`

## Repo quirks

* The repo directory is owned by a different Windows user. Run git with `git -c safe.directory=C:/repos/rangi ...` rather than changing global config.
* `*.bak` and `compiled/` are gitignored scratch files from DrRacket. Ignore them.
* Racket files use `#lang racket` or `#lang racket/base`. Prefer `racket/base` plus explicit requires for library modules (the reader must load fast at phase 1).
