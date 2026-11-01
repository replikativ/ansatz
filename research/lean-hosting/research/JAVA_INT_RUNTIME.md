# Signed Int runtime family

The research Java engine supports the nine Int extern roots in the original
1,514-declaration header inventory: ofNat, negSucc, neg, natAbs, add, sub, decEq,
decLt and decLe. Each has a genuine boxed wrapper in the pinned
[18-row fixture](../test/fixtures/java-int-runtime/README.md). Source is Lean
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; inventory membership is distinct
from executing an entire frontend path. Other Int arithmetic remains unsupported.

Int uses mathematical signed values carried by Long or immutable BigInteger.
This shares the existing OBJ lane and signed GraphInt transport. It does not
introduce constructor encodings, native tagged-int bits or native small-object
thresholds. Pointer identity for arbitrary source Int values remains outside the
certified pointer profile. Borrowed operations accept signed values directly;
Nat conversion inputs independently require nonnegative mathematical values.

Small signed arithmetic uses Long comparisons and checked addition/subtraction.
Overflow promotes to BigInteger; arbitrary-precision results normalize back to
Long when they fit. In particular, neg/abs(Long.MIN_VALUE) yields positive 2^63,
negSucc(Long.MAX_VALUE) yields Long.MIN_VALUE, and addition/subtraction never
wrap. NegSucc implements -(n+1), not signed negation alone. Int.natAbs returns a
nonnegative Nat carrier. Immutable numeric carriers have no manual guest Node
credits; JVM reachability owns their physical lifetime.

The exact original ABIs distinguish owned Nat conversions from borrowed signed
operations. Borrowed raw roots, partial applications, makeClosure and imported
closures reject; original owned boxed wrappers preserve the guest boundary and
support ordinary AP. Validation rejects nonnumeric Nodes before consumption.
Failed explicit execution retains the existing terminal cleanup restriction.

Eight focused tests cover each driver, with 351 recursive and 360 explicit
assertions: exact source/ABI pins, pairwise arithmetic/order over 100-bit values
and Long boundaries, unary and Nat conversions, overflow promotion and
normalization, borrowed entry/PAP/import fences, boxed partial application,
signed prepared-graph roots and fork, malformed Nat/Int values and unchanged
owned Node counts on failure. These are semantic/runtime tests, not evidence of
complete frontend execution or a performance comparison with compiled Lean.

The combined isolated jar gate passes 568 executions / 18,025 assertions across
65 suites at 384 MiB. Independent source/ownership review found no functional
blocker. No full Init/frontend image was restored for these checks.
