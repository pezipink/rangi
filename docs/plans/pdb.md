---
title: Portable PDB
description: Source lines for debuggers. The .line directive, the sidecar PDB, and the PE debug directory.
---

# Portable PDB

Rangi writes a portable PDB (PortablePdb-Metadata.md in dotnet/runtime) beside every image by default. It records sequence points from `.line` directives, the names of named locals, and the document table. Debuggers and stack traces can then show source lines. The PDB and the image are deterministic: the same input gives the same bytes.

Pass `#:debug? #f` to `assemble` or `write-image` to write neither the sidecar nor the debug directory. The image then has the same bytes as before PDB support.

## Scope

In scope: the `.line` directive, the portable PDB file, the sidecar `<name>.pdb` next to the output, the PE debug directory (data directory 6), and `#:debug?`.

Out of scope: reading PDBs, embedded PDBs (`EmbeddedPortablePdb`), Source Link, custom debug information, and async or iterator state machine maps. Strong naming is also out of scope.

## The `.line` directive

```
(.line startLine startCol endLine endCol "file")
```

A `.line` marks the instruction after it with a sequence point. It adds no IL bytes, so code is the same with or without it. The syntax is Rangi's own, following ilasm's style rather than its exact argument layout.

* Several `.line` directives at one offset keep the last one.
* A `.line` at the end of a method, with no instruction after it, is dropped.
* A method with no sequence points gets no debug data, so its locals signature is not written to the PDB.
* A `.line` is rejected when:
  * `startLine` is 0, or it is the hidden-line value `0xFEEFEE`. Line 0 is allowed by the spec, but Rangi rejects it for now.
  * a column is above 65535.
  * the end line is before the start line.
  * the span is empty (same line, end column not after start column).
  * the file name is empty.

## What is written

The PDB has the `#Pdb` stream and the portable-PDB tables 0x30 to 0x35:

* Document (0x30): one row per distinct file, in order of first use. The name is a document name blob with separator 0.
* MethodDebugInformation (0x31): one row per MethodDef. A method whose points all lie in one file names that document. A method spanning several files names none and gives its first file as InitialDocument. The sequence points blob follows the spec's delta encoding: the first point is absolute, a document change is a record with a zero offset delta, and the Δcolumn is unsigned when the Δline is zero and signed otherwise.
* LocalScope (0x32): one row per method with named locals, spanning the whole body. Rows are sorted by method, then start offset, then length descending.
* LocalVariable (0x33): one row per named local.

The `#Pdb` header holds the 20-byte PDB Id, the entry point, and the referenced-table bit vector. It lists only MethodDef (0x06) and StandAloneSig (0x11), and it records their row counts so the PDB's row references stay valid.

## The image side

The debug directory has three entries, in this order:

1. CodeView (type 2): `RSDS`, the Id's first 16 bytes as the GUID, age 1, and the PDB's basename as UTF-8, NUL-terminated. The entry's TimeDateStamp is the Id's last four bytes.
2. PdbChecksum (type 19): `SHA256\0` followed by the SHA-256 of the PDB file.
3. Reproducible (type 16): size 0.

The debug chunks are appended to `.text` after the entry stub. Earlier layout does not move. The CodeView path is the basename only, so the output does not depend on the directory it is written to.

## Simplifications

These are choices that a debugger does not need, or that differ from Roslyn. Each one is a deliberate decision, not an oversight.

* The PDB Id is a SHA-1 of the PDB with the Id zeroed. It is not a GUID or a timestamp, and it is not Roslyn's algorithm. The image and PDB still match, which SRM confirms.
* The checksum is the SHA-256 of the PDB file with the Id zeroed.
* The nil hash and nil language GUIDs are used in the Document rows, and `#GUID` is empty.
* ReferencedTypeSystemTables is the minimal set, {MethodDef, StandAloneSig}.
* There are no hidden sequence points. `.line` covers only the instructions the user marks.

## Verification

* `tests/il/line-directive-test.rkt`: the `.line` sequence points, zero IL bytes added, duplicate and trailing directives, locals, body-less methods, and error cases.
* `tests/oracles/pdb-srm-test.rkt` (SRM oracle, `tests/oracles/pdb-dump`): SRM reads the PDB version, entry point, both documents, every sequence point Rangi lowered, the nil document for a two-document method, and the debug entries. SRM associates the sidecar with the image. Two assemblies of the same program are byte-identical. With `#:debug? #f` there is no sidecar and no debug entry.
* PEVerify still passes on a debug-on image, and the program still runs.
* Snapshots: the debug directory and `.text` tail change every image's bytes. The regenerated snapshots are committed separately. With debug off, all 57 fixtures match their previous hashes.
* Facts about the debug directory and the PDB come from SRM and the spec, and are recorded in [verification.md](verification.md#spec-sources-and-discovery).

Not verified: whether a debugger shows the source lines (only SRM and PEVerify have run on the output), and whether the .NET Framework 4.7.1 CLR accepts the debug directory on every image.
