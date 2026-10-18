---
title: Shared type library plan
description: A canonical type reference and a provider interface, shared by reference assemblies and a module's own declarations, for type checkers running at phase 1
ms.date: 2026-10-18
---

## Goal

A language built on Rangi (for example Tui) needs to answer type questions at macro expansion time: what does `System.String` look like, does `Foo` implement `IEnumerable`, what does `List<int>.Add` take. Two sources answer them:

* **Reference assemblies**, read through the phase-1 reader (`src/cli/reader.rkt` and `src/cli/index.rkt`).
* **The module's own declarations**, collected from the forms the module has seen so far, filled in during pass 1 and resolved lazily.

This plan defines one type vocabulary that both sources produce and both consume, and one interface that a checker calls without knowing which source answered. Rangi owns the vocabulary and the reference provider. Each language owns its declaration syntax and feeds the declaration provider.

## Non-goals

* No parser. Languages use the s-expression reader, so the library only sees syntax objects that the language has already expanded.
* No IL emission. The library describes types. The writer keeps emitting bytes.
* No full CLR type loader. Generic instantiation and constraint checking are approximated until a language needs them. Each approximation is listed under open questions.

## Principles

* **Lazy, like the reader.** Opening a provider does no work. A type is decoded when a lookup asks for it, and the result is cached on the provider (the same lifetime rule as `asm-reader-cache`, see [AGENTS.md](../../AGENTS.md)).
* **Equal means identical.** Two references to the same type compare `equal?`, whichever provider produced them. Hash tables keyed by type work without a conversion step.
* **Refer by reference, never by copy.** A descriptor names other types with canonical references. It never embeds another descriptor. This keeps cycles (`class Node { Node next; }`) and cross-assembly graphs cheap.
* **One provider per assembly identity.** A module never reads its own output dll. The declaration provider is the only source for the module being compiled. A reference assembly is read once through a reference provider, keyed by its identity (name, version, culture, public key token).
* **Deterministic.** Member lists come back in metadata row order, or in declaration order for the declaration provider. Nothing iterates a mutable hash to produce output.

## Layer 1: canonical type references

A type reference is a small, immutable prefab struct, so `equal?` and `equal-hash-code` work on it directly, and it survives being quoted into a compiled module:

```racket
(struct type-ref (asm namespace name arity kind args) #:prefab)
```

* `asm` is the assembly name, for example `"mscorlib"`. A module's own types use the module's name, for example `"TuiModule"` in Tui. Core facades such as `System.Runtime` are answered by the mscorlib provider.
* `namespace` and `name` are strings. `name` never carries a generic suffix: `List` with arity 1, not `List`1. Nested types use `Outer/Inner` as the name.
* `kind` is `'class`, `'valuetype`, `'interface`, `'enum`, `'delegate`, or `'array`/`'pointer`/`'byref` for constructed forms. Recording the kind here means `int` and `System.Int32` are the same reference, and the checker never has to ask a provider whether a type is a value type.
* `args` is a list of type references for generic instantiations, empty otherwise. Generic parameters are a separate struct, `(type-param owner index)`, so an unbound `T` is not confused with a type named `T`.

Canonicalisation rules:

1. Primitive spellings (`int`, `Int32`, `System.Int32`, `int32`) reduce to one reference for `System.Int32`. The table lives in `src/types/canon.rkt`, and is the only spelling source.
2. Forwarders are not followed. A type is found in the assembly that defines it, and only when that assembly is in the env. See open question 9.
3. Type names are compared with ordinal string comparison. No culture-sensitive lowering.

## Layer 2: lazy descriptors

A descriptor is what a checker reads after it has a reference:

```racket
(struct type-desc (ref shape abstract? sealed? base interfaces methods fields) #:transparent)
```

* `ref` is the canonical reference, so a descriptor always knows its own identity.
* `base`, `interfaces`, `methods`, and `fields` are promises, so `force` decodes them on first access. Opening `System.String` does not decode `IComparable` until something asks.
* `methods` is a promise of `method-desc` values and `fields` of `field-desc` values. Each holds its signature as type references. Properties and events are not decoded yet.
* A descriptor is cached on the provider that built it. Asking twice returns the same object.

The reference provider builds descriptors from the R7 index (`find-typedef`, `typedef-methods`, `method-params`, `interface-impls`, `generic-params`, and so on). The declaration provider builds them from the forms the module has declared. Both produce the same struct, so the checker never branches on the source.

## Core API

Two functions carry the whole library. Members, base types, interfaces, and generic substitution all start from a descriptor, so everything else is built on these two.

```racket
; identifier in source -> type reference (layer 1)
(resolve-type-name env id)

; type reference -> descriptor (layer 2), from whichever provider owns its assembly
(env-type env ref)
```

* `env` is the per-module context. It holds the providers, the namespaces the module opens, and the descriptor cache. Languages create it in `%module-begin` and pass it to every checker call. The search order is described under the provider interface below.
* `resolve-type-name` turns an identifier into a canonical reference. It does not decode a descriptor, so it stays cheap on the hot path. The order it tries is under name resolution below.
* `env-type` routes on the reference's `asm` field, to the provider whose assembly has that name. Core facades go to the core library provider. It returns the cached descriptor, or `#f` for a reference that no provider can supply.
* Everything else takes a descriptor. Member lookup, base and interface walks, and generic substitution (`List<int>.Add` taking an `int`) all work on the output of `env-type`, and substitution returns new member signatures without changing the cached descriptor.

## Name resolution

`resolve-type-name` is the only place the two sources are told apart. It tries these steps in order and stops at the first that finds a type:

1. **Lexical binding.** If `(syntax-local-value id (λ () #f))` is a type binding, use its reference. This covers the module's own types, imported Racket modules, and macro-introduced names, all with hygiene. The failure thunk stops a plain variable from raising an error.
2. **Qualified name.** `System.Text.StringBuilder` is looked up in every provider, the declaration provider included.
3. **Opened namespaces.** The short name is tried under each namespace opened by `using` or `open`, in every provider.
4. **More than one match** is an ambiguity error, unless the language's policy decides. The policy is a parameter of `resolve-type-name`, so each language chooses its own rule, for example "local types shadow imported ones". The default policy, `error-on-ambiguity`, raises an error. Tui passes `prefer-local-policy`, so a local type wins. Unknown names return `#f`, and the caller reports the name the user wrote.

Step 1 comes first, so a local `Point` wins over an imported `Point` in the same scope. This matches C# and F#.

## The provider interface

```racket
(provider-find p ns name arity)         ; namespace, name, arity -> type-desc or #f
(provider-by-ref p ref)                 ; canonical ref -> type-desc or #f
(lookup-type e namespace name arity)    ; open reference of the first type named in any provider, or #f
```

Providers are plain structs with procedure fields, not `define-generics`. That avoids the `racket/generic` load cost on every phase-1 expansion. A provider is the struct `(provider asm find by-ref cacheable? declare)`: its assembly identity, its `find` and `by-ref` procedures, whether its answers may be cached, and for declaration providers a `declare` procedure.

Generic arity is a separate integer on the reference, never part of the name string. Metadata writes generic types as `List`1`, and a bare backtick is read by Racket as quasiquote, so a symbol with a backtick in source code would break. The reader boundary strips the suffix and stores the arity as data, so the backtick never reaches the library's names.

Both providers implement `find` and `by-ref`. Checkers never call a provider directly: `env-type` and `lookup-type` are the public way in. The `env` searches providers in this order:

1. The declaration provider for the module being compiled.
2. Reference providers, in the order the module's `using` forms named them.

A reference names one assembly, so it routes to one provider. A name that matches in several providers goes through the ambiguity policy in name resolution. A name that matches in none is "unknown type", with the name the user wrote.

The `env` is the only thing a checker calls. Tui and any later language use the same `env`, so a language cannot skip one of the two sources by accident.

## Declaration provider

* Lives in memory for one expansion. It is created by `%module-begin`, filled while forms are expanded in pass 1, and dropped at the end of expansion.
* Each declared class gets two bindings, from one descriptor object:

  ```racket
  (define d (make-decl-descriptor #'Point ...))   ; one object
  (decl-provider-add! local "Geo" "Point" d)      ; reachable by reference, through env-type
  #`(define-syntax Point (type-binding '#,ref))   ; reachable by name, through the binding
  ```

  The `define-syntax` binding is what step 1 of name resolution finds. The provider entry is what `env-type` finds by reference. `"Geo"` is the module's name, which is the assembly identity for its own types.
* The `define-syntax` binding stores only the type reference, which is prefab and so survives compilation. The descriptor stays in memory with the provider. Open question 3 covers a declaration provider that another module needs.
* Forms declare types through the provider's `declare-type!` and `declare-member!`. Declarations are recorded in declaration order, so the output is deterministic.
* A declared type is in state `'declared` until `complete-type!` runs. `declaration-state` reports `'declared`, `'complete`, or `#f` for an unknown type. `declare-member!` appends a method or field in declaration order and fails on a complete type or on a member whose owner is a different type, so the member lists come out in the same order every time.
* Information from `%module-begin` reaches the checker through the phase-1 state of the expansion (a value stored in the provider, found by `syntax-local` lookup from the module context), not through syntax properties. Syntax properties are still used for source locations and for marking which forms declared what.

## Reference provider

* One per assembly. `open-reference-provider` takes a path, opens the image through the Rangi reader, and builds nothing until a lookup runs.
* Built on `src/cli/index.rkt`. The reader's index caches stay on the reader, so a reference provider and the reader share one lifetime.
* Lookups never scan the whole image. A name lookup uses the R7 name index. Members come from the owner ranges, not from a full table walk. `find` answers only public types, so internal types are invisible to name lookup. `by-ref` does not check visibility.

## Performance budget

Phase 1 runs on every keystroke in DrRacket, so the library must meet these budgets, measured with the same method as `tests/read-bench-test.rkt`:

* Opening a reference provider: no more than the reader's open time (about 2 ms for mscorlib on this machine).
* First lookup of a type: no more than the R7 first-lookup cost (about 2 ms, including the name index).
* Warm lookup of a cached reference: well under 1 µs.
* Building a descriptor for one type with 50 members: under 100 µs.
* Nothing is decoded that a checker did not ask for. A test counts reads to confirm this for `System.String`.

Any change that misses a budget needs a benchmark row in the same commit, and the change is explained in the commit message.

Measured with `experiments/types-bench.rkt` (mscorlib 4.7.1 reference assembly, 20 runs each, medians):

| Measure                                              | Median        | Range (min to max)   | Budget        |
|------------------------------------------------------|---------------|----------------------|---------------|
| Open a reference provider                            | 1.3 to 2.2 ms | 1.1 to 8.9 ms        | about 2 ms    |
| Open plus first lookup of `System.String` (cold)     | 3.9 to 4.3 ms | 3.1 to 5.5 ms        | about 2 ms    |
| Warm lookup of a cached reference, per call          | 0.26 to 0.43 µs | 0.23 to 0.47 µs    | well under 1 µs |
| Decode all 168 methods and fields of `System.String` | 0.35 to 0.47 ms | 0.33 to 1.0 ms     | under 100 µs for 50 members |

The numbers vary between runs on this machine, so the ranges matter. Open is at the budget edge, and cold open plus the first lookup is over it, so the open-time overrun stays open. The 50-member row is not measured on a 50-member type. Scaling `System.String` (168 members) gives about 0.14 ms for 50 members, which is over the budget, so it is also open. The 5.5 ms open figure from `experiments/generic-list.rkt` was a single cold run and is not comparable to these medians.

## Module layout

* `src/types/canon.rkt`: `type-ref`, `type-param`, the primitive table, `with-args`, `with-asm`, and `type->string`.
* `src/types/desc.rkt`: `type-desc`, `method-desc`, `field-desc`, substitution (`subst-type`, `subst-method`), and `instantiate-desc`.
* `src/types/provider.rkt`: the `provider` struct, `env`, `env-type`, `lookup-type`, `resolve-type-name` with its policies, `find-methods`, `make-declaration-provider`, and `declare-type!`.
* `src/types/reference.rkt`: `open-reference-provider`, the reference provider built on the Rangi reader.

Only `reference.rkt` may require `src/cli/`. The other three files do not, so a language can load the vocabulary without the reader.

Tests are in `tests/types/` (30 tests across the four files). The `List<int>` demo is `experiments/generic-list.rkt`.

## Checklist

* [x] Core API: `env`, `resolve-type-name` (layer 1, no descriptor decode), and `env-type` (layer 2, routed on `asm`), with tests for both
* [x] Canonical `type-ref` and `type-param` structs (prefab), with tests for `int` and `System.Int32` giving the same reference
* [x] Primitive table and canonical identity strings for assemblies
* [x] Forwarders dropped from this plan: they are not followed (open question 9)
* [x] Lazy `type-desc`: base, interfaces, methods, and fields are promises
* [x] Read-count test on `System.String`, showing nothing is decoded that a checker did not ask for
* [x] Reference provider over the Rangi reader, cached in the env for cacheable providers
* [x] Declaration provider: `make-declaration-provider` and `declare-type!`
* [x] Declaration provider: `'declared` state, `declare-member!`, and insertion-ordered member output
* [x] `env` search: providers in order, with the ambiguity policy and `lookup-type`
* [x] Name resolution: lexical binding first, then qualified names, then opened namespaces, with the ambiguity policy passed as a parameter of `resolve-type-name`
* [x] Equivalence test: the same type from the reference and the declaration providers gives equal descriptors where the members match
* [x] Performance budgets above checked in `experiments/types-bench.rkt`, with numbers recorded here (cold open plus first lookup and the 50-member extrapolation are over budget and stay open)
* [x] Tui's `private/clr.rkt` moved onto `env`, with both examples and all Tui tests passing
* [x] `raco test tests/` green in rangi and tui

## Open questions

These are decisions to make before the matching checklist item, not blockers for the first two items.

1. **Generic instantiation.** Answered for type parameters: `List<int>.Add` takes an `int`, while the emitted member reference keeps the open signature (`Add(!0)`), as the CLR requires. Still open: method-level parameters (`!!0` stays unsubstituted) and nested generic arguments such as `List<List<int>>`, which need a recursive substitution pass. This is the hard, recursive part.
2. **Constraints.** Constraint checking is out of scope until a language needs it. Should the descriptor store constraints now (cheap to read) so later checks do not need a new decode path?
3. **Declaration-provider lifetime.** Is per-expansion correct, or should a language keep a declaration provider per module across expansions, invalidated on save? The first is simpler and matches the build-on-save idea; the second is faster for DrRacket but needs an invalidation rule.
4. **Where the declaration provider lives.** This plan puts it in Rangi as a generic container and leaves each language to fill it. Should the container also own the declaration syntax conventions, or stay purely data?
5. **Forwarders into the module.** If a reference forwards to a type in the module being compiled, which provider wins? The plan says ambiguity is an error; confirm that is what we want.
6. **Pointer tables.** Closed. Member ranges map through the `#-` pointer tables (R7 in restructure.md), and the reference provider reads through them.
7. **Serialisable descriptors.** Answered: the binding holds only the prefab `type-ref`, and `env-type` resolves the descriptor through the provider.
8. **Ambiguity policy.** Answered: the library default is `error-on-ambiguity`, so a language must choose a policy. Tui chooses `prefer-local-policy(asm, first-match-policy)`: a local type wins, and otherwise the first candidate is taken, as the old Tui code did. `first-match-policy` is available to any language that wants that rule.
9. **Forwarders.** Not followed. Core facades are answered by the mscorlib provider (`core-facades`). Any other forwarded type is missing unless its defining assembly is in the env. Following forwarders, with a cycle guard, is the fix when a language needs types that live in other assemblies.
10. **Override and hiding.** `find-methods` walks the base chain and returns every match by name. It does not apply overrides or `new` hiding, and a missing base silently ends the walk. Overload resolution needs both to be correct.
11. **Dropped signature details.** modreq and modopt are stripped, bounded array bounds are dropped, and function pointers raise an error. Constructed kinds (arrays, pointers, byrefs) are not modelled in Tui.
