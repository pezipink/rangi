---
title: Opcodes and IL assembler plan
description: Plan for a complete ECMA-335 Partition III opcode table, verified against System.Reflection.Emit, plus labels, branch relaxation, and method body encoding
ms.date: 2026-10-17
---

## Current state

`encode-il` in `src/cli/lower.rkt` lowers the parsed model with the shared opcode table (`src/il/opcodes.rkt`) and the encoders in `src/il/encode.rkt`. Labels and branch relaxation come from `src/il/labels.rkt`, and maxstack from `src/il/stack.rkt`. `call` targets a MemberRef, a same-module static MethodDef (`(call ret (Class) name (params))`), or a MethodSpec for a generic method. `callvirt` on a same-module method is rejected, because local methods are static. Supported beyond plain opcodes: `.locals`, labels, `ldstr`, `switch`, and EH clauses `catch`, `finally`, and `fault`. `filter` is not supported. The `ops-*` fixtures (`ops-arith`, `ops-branch`, `ops-constants`, `ops-conversions`, `ops-eh`, `ops-eh-finally`, `ops-locals-args`) are checked with PEVerify and ILVerify.

## Target size

`System.Reflection.Emit.OpCodes` on .NET 10 exposes 226 opcodes: 199 one-byte and 27 two-byte (`FE xx`). This count includes the reserved `prefix1`-`prefix7` and `prefixref` entries, which must not be emitted. ECMA-335 also defines `no.` (`FE 19`), which Reflection.Emit does not expose. The 17 operand types are:

| Operand type          | Encoding                                               |
|-----------------------|--------------------------------------------------------|
| `InlineNone`          | none                                                   |
| `ShortInlineI`        | int8                                                   |
| `InlineI`             | int32                                                  |
| `InlineI8`            | int64                                                  |
| `ShortInlineR`        | float32                                                |
| `InlineR`             | float64                                                |
| `ShortInlineVar`      | uint8 local or argument index                          |
| `InlineVar`           | uint16 local or argument index                         |
| `ShortInlineBrTarget` | int8 offset from the end of the instruction            |
| `InlineBrTarget`      | int32 offset from the end of the instruction           |
| `InlineSwitch`        | uint32 count, then count int32 offsets from the end of the instruction |
| `InlineMethod`        | MethodDef, MemberRef, or MethodSpec token              |
| `InlineField`         | Field or MemberRef token                               |
| `InlineType`          | TypeDef, TypeRef, or TypeSpec token                    |
| `InlineTok`           | any of the above (`ldtoken`)                           |
| `InlineString`        | `#US` token (0x70)                                     |
| `InlineSig`           | StandAloneSig token (`calli`)                          |

## Steps

### O1 Opcode table as data

* [x] Write `tests/oracles/opcodes-dump` (a single-file `dotnet run` program) that prints every `OpCode` as `name size byte1 byte2 operand-type flow-control stack-pop stack-push opcode-type`, sorted by value. Commit its output as `tests/fixtures/opcodes.tsv`.
* [x] Write `rangi/il/opcodes.rkt` as a literal table, one entry per opcode: symbol (`ldc.i4.s`), bytes, operand kind, flow control, stack pop and push behaviour. Use ECMA-335 Partition III names, which match Reflection.Emit names with `_` replaced by `.`.
* [x] Add a unit test that asserts the Racket table equals `opcodes.tsv` (minus reserved prefixes, plus `no.`). This is the completeness and correctness gate.

### O2 Operand encoding

Status: encoders in `src/il/encode.rkt` (stream B) cover every operand kind; tests in `tests/il/encode-test.rkt`. Front-end syntax and token resolution are still open.

* [x] One encoder per operand kind, driven by the table, so adding an opcode never needs new assembler code.
* [ ] Operand syntax in the s-expression front end:
  * numbers for `I`, `I8`, `R`
  * symbols or integers for variables (`(ldloc x)`, `(ldarg 0)`)
  * label symbols for branches and `switch`
  * method, field, and type references as structured forms that the CLI layer turns into tokens (the existing `(call void (mscorlib System.Console) WriteLine (int32))` style)
  * strings for `ldstr`, which intern into `#US`

### O3 Labels and branch relaxation

Status: label resolution and fixed-point relaxation in `src/il/labels.rkt` (stream B) are done; tests in `tests/il/labels-test.rkt`. The `ldc.i` writer replacement is still open (O4).

* [x] Labels are `(label name)` forms or `name:` symbols in the instruction stream.
* [x] Assemble with all branches short, measure, then iteratively widen any branch whose offset does not fit in int8 until a fixed point. Long forms are never shrunk back, which guarantees termination.
* [x] Provide macro forms that pick the shortest encoding: `ldc.i4` -> `ldc.i4.m1`, `ldc.i4.0`-`ldc.i4.8`, `ldc.i4.s`, `ldc.i4`; `ldloc`/`stloc`/`ldarg`/`starg`/`ldloca`/`ldarga` -> `.0`-`.3`, `.s`, long. Keep explicit forms available for exact control. (Selectors `encode-ldc-i4` and `encode-var-access` in `src/il/encode.rkt`; not yet exposed as front-end names.)
* [~] Replace today's `ldc.i` with the `ldc.i4` macro; add `ldc.i8`, `ldc.r4`, `ldc.r8`. The `ldc.i8`, `ldc.r4`, and `ldc.r8` forms are in use (`ops-conversions`). The `ldc.i4` macro is not yet exposed to the front end, so `ldc.i4.s` and the other explicit forms are written by hand.

### O4 Method bodies (II.25.4)

* [x] Tiny header when code is under 64 bytes, maxstack is at most 8, there are no locals, and there are no exception handlers. Otherwise use a fat header: flags `0x3003` with `InitLocals` as needed, maxstack, code size, and a `LocalVarSigTok`. Fat headers without locals are covered by `text-over-400` and `text-over-2000`; `InitLocals` and `LocalVarSigTok` are covered by `ops-locals-args` and `ops-branch`.
* [x] `.locals` -> local variable signature blob (`0x07`) -> StandAloneSig row -> token.
* [~] Exception handling sections (`.try`, `catch`, `finally`, `fault`, `filter`) with small (12-byte) or fat (24-byte) clause encoding chosen by offset sizes. Each section is 4-byte aligned after the code.
  * [x] Syntax: `(.try (catch (asm ty)) ts te hs he)`, `(.try (finally) ts te hs he)`, `(.try (fault) ts te hs he)`. Clauses are written in source order, so inner clauses come before enclosing ones. The form mirrors the existing `catch` form. `endfault` is accepted as an alias for `endfinally` (both are 0xDC, III.4.5 and III.4.6).
  * [x] Flags: catch 0x0000, finally 0x0002, fault 0x0004 (II.25.4.6). The class token is 0 for finally and fault.
  * [x] Handler entry stack depth (III.1.7.5): catch 1 (the exception object), finally and fault 0. This feeds `compute-max-stack`.
  * [x] `filter` (0x0001): `(.try (filter <label>) ts te hs he)`. The class token is the filter block offset. Filter blocks come before their handler and end in `endfilter` (0xFE 0x11). The filter entry depth is 1 (II.25.4.6, inferred; see the open items in the lane report). Fixture `ops-eh-filter`.
* [x] Compute maxstack by abstract interpretation over the opcode table's stack behaviour and the control flow graph, unless `.maxstack` is given. Report stack underflow and inconsistent depths at merge points as assembly errors. An explicit `.maxstack` must be at least the computed depth (`tests/il/stack-test.rkt`).
* [x] Prefix validation: `unaligned.`, `volatile.`, `tail.` (must be followed by `ret`), `constrained.`, `readonly.`, and `no.` must precede an instruction they apply to. Labels are skipped when checking. `constrained.` is still rejected by `check-passable`.

### O5 Verification

* [x] Unit tests per operand kind and per macro boundary (`-1`, `0`, `8`, `9`, `127`, `128`, `-128`, `-129`). Merged from `stream/b-tests` in `tests/il/operand-boundary-test.rkt`.
* [x] Branch relaxation tests with a branch exactly at the int8 limit (127 and 128 bytes). In `tests/il/relaxation-boundary-test.rkt`.
* [ ] An `il-all-opcodes` fixture that uses every opcode at least once in valid, verifiable (where possible) code, run through ildasm and the SRM dumper. Unverifiable opcodes (`cpblk`, `localloc`, `jmp`, `calli`, `arglist`) go in a separate fixture that checks PEVerify `/md` only.
* [ ] ILVerify on every IL fixture. Execution tests exist for loops, catch, finally, fault, filter (`ops-branch`, `ops-eh`, `ops-eh-finally`, `ops-eh-filter`), `ldstr-hello`, and `switch-dispatch`. Not every fixture is covered yet.
