# Checked Array.set! runtime unit

This narrow research unit implements original `lean_array_set` at intrinsic 518. It preserves the exact native ABI: erased, owned object, borrowed tobject Nat, owned tobject replacement → owned object. Intrinsic 517 implements the independent Level metavariable operation. No common Node field or new scheduler/provider API is introduced.

Pinned Lean 4.33.1 commit 819816b2 supplies `Init/Data/Array/Set.lean:54`, `include/lean/lean.h:1070–1077`, and `runtime/object.cpp:532–534`. The two authentic raw/boxed declarations and source hashes are recorded in [the fixture](../test/fixtures/java-array-set-runtime/README.md).

In bounds, this uses existing array logical-size, ownership/alias validation and exclusive/COW storage. Shared, persistent and logical-MT arrays copy live edges before dropping the input array. The replacement transfers into exactly one field; the old field loses one credit. Positive old-value/replacement aliases require their independent incoming credit. The borrowed Nat uses existing immutable logical Long/BigInteger carriers; it is not retained, consumed or truncated to an unsigned machine index.

Active explicit sessions use the existing native action continuation and release-before-store sequence. A Promise drop/finalizer can suspend before the replacement store; output, replacement, index/cursor, release-claim state and continuation use the existing same-memo fork path. No callback or store is replayed. Inactive finalizer-free behavior uses the same existing FSET/USET synchronous path and retains its documented failure-cleanup limits.

Out-of-bounds, including huge Nat indices, raises `Array.set! panic path outside bounded runtime profile` before primitive allocation, RC or store effects. This intentionally does not execute the native panic handler, release replacement as a fake panic implementation, emit output, or return the pure source fallback. Direct root and complete AP entry validate before publishing/consuming captures, even with inactive task runtime. A real owning boxed wrapper or enclosing guest frame may already have executed earlier instructions before it reaches the primitive; no whole-invocation rollback is promised. Negative Nat, wrong array/value carriers and bad erased placeholders reject as invalid operands.

The new focused namespace `java-ir-array-set-checks` covers exact ABI/provenance, original wrapper, Long/BigInteger indices, unique/shared/persistent/logical-MT storage and fork isolation, valid/invalid replacement aliases, panic-domain preflight, inactive AP capture preservation, and active Promise cleanup through Host suspension/fork on raw, original boxed and AP routes. Synthetic rows/host callback are bounded ownership models, not additional original Lean code.

Root validation compiled the frozen Java source with Java 11 and a 256 MiB compiler bound, then passed all seven focused tests / 140 assertions in each of the default and explicit drivers in the retained JVM. Frozen source SHA-256: `06ba8cf2214bc4e2bab3876478bf19d06e40e8fa8da691ae07200b7b51b748bb`; isolated test jar SHA-256: `b15fd1d2747a177a8a8c952956dc5228cd118573fcd9be401f7f63cf0de7391d`. Independent source/fixture review found no blocker. No original frontend theorem completion is claimed by this unit.


The combined integration preserves the merged Level operation and its root/AP
preclaim gates. Java source SHA-256
`710b2981fa3e5b49e2652d4bf14c0354bdda12fa92927f69dffb362be37c5f20`
compiled to immutable jar SHA-256
`32783cee2ece08e2eb39fbdf0597bca6874886f43b5f5bf85dc08e1c8420426f`.
The retained JVM passed both seven-test array groups and the existing 20-test
Level group on that artifact. Its separate 384 MiB combined gate exited 0:
113 result families, 1,109 test executions, 53,840 assertions, zero failures/errors.
Campaign log `java-array-set-integration-v1/combined-gate-v2.out` has SHA-256
`19e36d3c4a74732d9020bfb7603ea7616a97d8b38f5df35b040d589bd06c17a7`.

The original frontend then executed this operation during term-theorem processing
and advanced to the distinct `Lean.Expr.findExtImpl?` boundary, after two checked
axioms and before its first theorem admission. It reused the same authenticated
523-global image; no new image or unchecked theorem publication was substituted.
