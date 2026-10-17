# Development workflow

How to move through the plans quickly without breaking what already works. Written from measured timings on Wave 1 (see [roadmap.md](roadmap.md)). Follow it unless a change says otherwise.

## Principles

* **Speed over exhaustive checks mid-section.** New CLI coverage (new opcodes, table columns, signature forms, fixtures) rarely breaks existing output. Run the targeted tests for the lane and catch regressions at the section boundary, not on every commit.
* **Full suite at section boundaries.** Run the whole suite once when a section (a wave or a phase) closes, and before any merge into `main` that changes emitted bytes in shared code (`src/pe/`, the metadata writer, `src/cli/lower.rkt`).
* **Parallelise by file, not by idea.** Two lanes can run at once only if they touch disjoint files. Check the hot spots below before splitting work.
* **Keep the plans current.** Tick the checklist in the plan you worked on in the same commit.

## Lanes

A lane is one narrow objective with its own git worktree and branch, handed to one background agent.

```powershell
git worktree add -b lane/<name> "$env:TEMP\rangi-lanes\<name>" main
```

* Lane agents run only the targeted tests for their change (see below), commit on their branch, and report the branch name.
* The coordinator merges lanes into `main` one at a time with `git merge --no-ff lane/<name>`, then removes the worktree and branch (`git worktree remove --force` is safe after a merge).
* Merge order: take the lane that touches shared hot spots first, so the others rebase onto it.
* The coordinator runs the full suite once after all lanes of a wave are merged.

### Hot spots (serialise these)

These files are edited by almost every opcode, table, or fixture change. Two lanes that edit them conflict.

* `src/cli/lower.rkt` (IL lowering, exception regions)
* `src/ilasm/syntax.rkt` (assembler syntax and validation)
* `src/cli/reader.rkt` (table decoding and the public re-exports)
* `src/cli/schema.rkt` and `src/cli/tables.rkt` (the single source of truth for row layouts and coded indexes)
* `src/cli/metadata.rkt` (metadata writer)
* `docs/plans/cli-coverage.md` and `docs/plans/roadmap.md` (merge conflicts in checklists)

When a lane needs a hot spot, put it in the lane that owns that objective and keep other lanes away from it. Plan docs are updated by the coordinator at merge time, not by each lane.

## Test tiers

| Tier | Command | When | Wall time (Wave 1 machine) |
|------|---------|------|-----------------------------|
| Targeted | `RANGI_FIXTURES=<name>[,<name>] raco test <file>` | during a lane, after each change | seconds to a minute |
| Area | `RANGI_SKIP_CORPUS=1 raco test -j 4 tests/` | while a lane is still iterating on shared code | about 31 s (953 tests) |
| Section | `RANGI_REQUIRE_ORACLES=1 raco test -j 4 tests/` | at each wave or phase boundary, before merging shared-code changes | about 53 s |
| Snapshot | `RANGI_UPDATE_SNAPSHOTS=1 raco test tests/` | only when emitted bytes change on purpose; explain in the commit | serial, slow |

Notes:

* `RANGI_REQUIRE_ORACLES=1` makes a missing oracle tool an error. Use it for section runs and leave it off for quick local checks.
* `RANGI_SKIP_CORPUS=1` skips the reader corpus (`tests/oracles/reader-corpus-test.rkt`). It is the single longest file and sets the floor for any `-j` run. Never skip it at a section boundary.
* `RANGI_FIXTURES` filters only fixture-based tests. Oracle files that do not use fixtures still run in full, so pass a single file to `raco test` as well when you want the fastest loop.
* `-j 4` is safe for tests because each test writes to its own temp files. The oracle builds are the exception and are guarded by a lock (below).
* Do not run `raco make -j 4 tests/` on Windows. It fails with "open-input-file: Access is denied" because it tries to open a directory. `raco test` compiles the files it needs as it runs, so skip the separate compile step. If you see "instantiate-linklet: mismatch" after changing a struct's arity, run `raco test` on the changed files to recompile them.

## Oracle builds and the build lock

`build-srm!` (SRM dumper) and the ilverify test both run `dotnet build` in fixed `bin/` and `obj/` folders. Parallel test processes would race on them. `tests/lib/dotnet-build.rkt` serialises those builds with a machine-wide file lock (`rangi-dotnet-build.lock` in the temp directory). After the first build each one is an incremental no-op, so the lock adds little time. Do not call `dotnet build` on these projects directly from a test; go through `dotnet-build!`.

## Fixture and verifier conventions

* `<Module>` is special. If `<Module>` has any members, `parse-il` (`src/ilasm/syntax.rkt`) moves every member into a generated `Program` class and leaves `<Module>` empty. So a static field or helper on `<Module>` cannot be found by `(ldsfld <Module> ...)` or `(call ... (<Module>) ...)`. Keep `main` in `<Module>`, and put helpers and fields in named classes such as `Helpers` or `Store`. Changing this rule would change existing snapshots, so decide that deliberately.
* Verifier limits. ILVerify (.NET Core) does not implement TypedReference (`mkrefany`, `refanyval`) or `calli`. PEVerify rejects `calli` on an `ldftn` pointer (`Instruction cannot be verified`). These are verifier limits, not image errors. Keep such instructions out of verified fixtures.
* `tests/lib/fixture.rkt` lists `unverified-fixtures`. The PEVerify test runs those with `/md` only, and the ILVerify test skips them. Both still run the fixture's stdout check. Add a fixture to the list only when a verifier cannot accept its IL on purpose or by limit, and say why in the list comment.
* Runtime-only check. A fixture that neither verifier accepts is still run for stdout and exit code. That covers the instruction's behaviour, which is the point of the fixture.

## Timings we measured

* Wave 1 had four narrow lanes. Agent time per lane: 250 s (ldstr-switch), 265 s (field-sigs), 271 s (pe-constants), 600 s (p4-close, which had more to read). Wall time for the wave was about 10 minutes.
* Wave 2 slice 4 (`il-all-opcodes`) needed three oracle rounds. The first ILVerify run found TypedReference and `calli` limits, and the second PEVerify run found the `calli` limit on `ldftn`. Each round costs one oracle run, so run the verifiers on a new fixture early.
* A serial full suite and a `-j 4` full suite both pass. `-j 4` runs in about 53 s. The full suite with oracles passed 1137 tests after slice 4.
* Rough planning figure for a lane that adds a new opcode group, table column, or signature form: 5–10 minutes of agent time, plus about 2 minutes for the coordinator to merge and run the section suite. Lanes that touch the PE writer or DLL output take longer because failures there are harder to diagnose.

## Checklist for a lane agent

1. Work in your own worktree, on your own branch.
2. Read the plan section you are implementing and the spec citations it names.
3. Make the smallest change that completes the item. Cite ECMA-335 sections in comments where code encodes a rule.
4. Add or extend a fixture under `tests/fixtures/` for new behaviour. Run it with `RANGI_FIXTURES=<name>` first.
5. Run the targeted test file for your change. If you touched shared code, also run `RANGI_SKIP_CORPUS=1 raco test -j 4 tests/`.
6. Tick the plan checklist items you completed, commit with the Co-authored-by trailer, and report the branch name and what you ran.
7. Do not merge into `main` yourself unless the coordinator asked you to. Do not run the full section suite; the coordinator does that.

## Checklist for the coordinator

1. Read the roadmap and pick the wave. Choose lanes whose files do not overlap the hot spots they share.
2. Launch lanes as background agents. Keep working on independent items while they run.
3. Merge each finished lane with `--no-ff`. Resolve conflicts in plan docs by hand.
4. Run `RANGI_REQUIRE_ORACLES=1 raco test -j 4 tests/` once the wave is merged. Fix or revert before the next wave.
5. Update [roadmap.md](roadmap.md) (Status, Done list) and the relevant plan files in one commit.
6. Remove worktrees and branches for merged lanes.
