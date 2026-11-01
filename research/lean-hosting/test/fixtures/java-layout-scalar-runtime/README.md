# Original layout/scalar rows

`original-rows.json` preserves sixteen accepted catalogue records, including all
original row fields and `pretty`. Every record's `sha256` was checked against the
raw CAS bytes and the parsed raw row was compared exactly. `provenance.json`
records the accepted index, pinned Lean commit, source hashes, and this fixture's
hash. These are original exported IR rows, not native frontend execution receipts.
The accompanying LICENSE is the pinned upstream Apache 2.0 license.

The first twelve records are six raw/boxed pairs, in this order:

1. `Lean.IR.Checker.getMaxCtorFields`
2. `Lean.IR.Checker.getMaxCtorScalarsSize`
3. `Lean.IR.Checker.getMaxCtorTag`
4. `Lean.IR.Checker.getUSizeSize`
5. `UInt32.decLt`
6. `UInt64.toNat`

The four following records (`UInt16.decEq` and `UInt16.toNat`, each with a boxed
wrapper) are metadata evidence for a separate lane extension. They are deliberately
excluded from executable preparation. This fixture does not enable UInt16.

The four layout results describe the pinned 64-bit Lean target ABI: 256 object
fields, 1024 scalar bytes, constructor tag limit 243 and USize width 8 bytes. They
do not measure Java object sizes. Their domain is canonical Unit zero. UInt32
comparison operates on validated zero-extended values. UInt64-to-Nat preserves
all bits as logical nonnegative Long/BigInteger values; the original boxed wrapper
consumes a real scalar-box Node. This is not a native physical Nat representation
or allocation-parity claim.

Expected values in the focused checks come from pinned source, not a newly run
native oracle. The author performed no native or interpreter JVM execution.

`LayoutScalarOracle.lean` is an optional small native reference source. Run it
with the pinned official Lean toolchain using `lean --run` and these eight
arguments: `0 2147483647 2147483648 4294967295 0 9223372036854775807
9223372036854775808 18446744073709551615`. It prints the four layout limits, the
16 ordered U32 comparisons, and four U64 Nat results. Inputs are parsed at runtime.
Its source hash is pinned in provenance; no observed output is shipped yet.
