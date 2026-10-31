# Canonical UInt16 execution lane

UInt16 is appended as lane6; all earlier lane numbers remain unchanged. Two exact
native bindings are added: UInt16.decEq540 and UInt16.toNat541. The former returns
canonical Bool0/1; the latter canonical nonnegative Long. No other UInt16 natives,
Float32, kernel classes, Node fields or importer behavior are added.

The audit covers metadata and executable type parsing; canonical unsigned input;
width2 scalar projection/store with checked little-endian offsets; immediate
box/unbox; literal normalization; distinct lexical argument/join/return lanes;
case tags; original FAP/boxed PAP/AP; scalar cache; Code argument snapshots and
resume; Host public arguments and preclaim reply checks; AP/Host result boxing;
root results and same-memo fork. Generic nonOBJ control paths reuse their existing
implementation and preserve U16 type metadata. There is no U32 coercion.

The canonical scalar profile is deliberate: root inputs, unboxed values and IR
literals must be 0…65535. Pinned C++ IR literal loading does not narrow all small
unsigned types, so arbitrary malformed/wide raw literal parity is not claimed.
Source UInt16 arithmetic/conversion normalization outside these two native ABIs
is not added. Generic Float32 rejection remains intact.

The fixture retains the four exact original raw/boxed rows with accepted index,
raw hashes, typed Name membership, source pins and Apache license. The old
layout/scalar fixture's final four metadata assertions now check declaration Name
identity rather than permanently assuming UInt16 unsupported. Its six-operation
semantics are unchanged; the new lane suite verifies executable UInt16 directly.

Compiled checkpoint: Java SHA
`d0d4f71ee350c28e4fde79f80dfb257ac745ddd1844bfab19ad8440d3c954947`,
immutable Java11 jar SHA
`82765b9b2caa092b98a3f06fe508d9998fc31f406122977dce8cf61f456508c6`.
Independent source review found no missing lane/transport branch. The author ran
bounded javac, source/fixture and diff audits; no interpreter JVM/native program.
The ten focused tests cover raw/original boxed calls, boundaries, FAP/JMP/case,
PAP/AP scalar boxing, malformed lanes, packed adjacency/bounds/fork, Code/Host
suspension and invalid reply preclaim. Explicit-only control tests also fork a
claimed U16 HostCompletion while borrowed cleanup is pending and verify the scalar
result is published only after both branches drain. These use modeled ordinary
callers around the authenticated original operations. Parent execution evidence
and combined integration remain separate observations.

A systematic legacy test scan also adapted header, Float and guest-export tests
that formerly classified UInt16 as unsupported; Float32 rejection remains tested.
No existing semantic test was relaxed to accept cross-lane coercion. The optional
UInt16Oracle.lean takes six runtime inputs and prints exact Nat/equality results;
its source hash is pinned, with no unobserved native result claimed.

Parent-retained focused execution passed all ten tests in each driver on the
unchanged reviewed source/jar: recursive 134 assertions and explicit 157, zero
failures/errors at 384 MiB. Receipt
`target/java-u16-runtime-v1/focused-v2.out` has SHA
`a25ec49bdba13d003d5e1f27f9d611f7d944179db74220ece75656254288ccc0`. Initial context users failed before execution because a model
PAP used a single dotted Name component instead of the authentic hierarchical
Name; only those fixture references were corrected. No runtime guard or typed
Name matching was changed. The clean runner adds two count-guarded groups10/10
after the existing prerequisites. Combined current-backend validation and native
oracle execution are separate parent gates, not claimed by this focused result.
