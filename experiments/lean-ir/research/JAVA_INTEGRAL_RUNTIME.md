# Unsigned integral runtime tranche

The Java engine implements all 23 USize/UInt32/UInt8 extern declarations in the
bounded original header inventory, including seventeen new exact registry
entries and six existing ones. All twenty-three genuine boxed wrappers are
preserved in the [fixture](../test/fixtures/java-integral-runtime/README.md).
Source semantics come from Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, not the moved local checkout.
This is an explicit inventory subset, not every integral operation in Lean.

USize uses the existing distinct usize lane with raw 64-bit storage. Java negative
long bit patterns are valid internally; public scalar inputs remain unsigned
mathematical values and high-bit outputs become positive BigInteger. Addition,
subtraction and multiplication wrap modulo2^64. LT/LE use unsigned comparison.
Shifts mask the distance modulo64; right shift is logical. AND operates on bits.
ToNat and repr preserve the mathematical unsigned value, including2^64-1.

UInt32 addition masks to32bits, conversion toUInt8 keeps its low8bits, and its
borrowed Nat/proof conversion validates the erased slot before taking low32bits.
UInt8 equality/order/AND and tagged ToNat keep0..255. Existing USize.ofNatLT also
checks its erased proof slot; borrowed Nat conversions do not become consuming
*_of_nat_mk operations. Primitive scalar inputs have no Node owners; original
boxed wrapper inc/dec and USize box layouts remain authoritative.

The new primitives reuse scalar dispatch and the existing lanes. UInt64, Float,
signed Int, absent inventory div/mod operations and native resource behavior
remain separate support. USize and UInt64 will remain distinct typed IR lanes
when UInt64 is implemented, even though both use64-bit storage.

Six tests / 605 assertions pass per driver. The combined isolated jar gate passes
474 executions / 16,380 assertions across 57 suites at 384 MiB. Direct and genuine boxed calls cover
small/high-bit/max values, modular arithmetic, unsigned order, shifts0/63/64/65/
max, narrowing and Nat wrap, invalid public scalar/proof domains, and independent
packed-word mutation after fork. Independent source/fixture/ABI review is clear.

A paired retained-JVM computational control compares the earlier native-ref
artifact with this runtime, without frontend loading. Seven alternating-order
batches per driver give median allocation1,515,859.52 versus1,635,091.52 bytes/run:
+119,232 bytes, about7.9%. The array runtime added a live-size field to the shared
Node layout; this is a structural layout cost to address in a separate variant-
metadata change. One shared-machine observation measured recursive medians1.86/
1.97ms and continuation medians2.38/2.18ms, prior/current. These mixed timings do
not establish speedup or a stable CPU-overhead estimate. Full paired results are
in the measurement record; allocation is the actionable result.

The five-global header probe reaches41 original bodies and1,579 instructions
before missing the captured Lean.attributeMapRef. A separately verified six-root
companion imports/forks49,645 nodes and2,631 headers in the384MiB REPL. It reaches
71 original bodies and2,128 instructions, then pauses for code whose preparation
needs the currently unsupported uint64 lane. This distinguishes missing captured
state from lane coverage. The all-sentinel fixed-point probe separately discovers
a ByteArray representation requirement; it is not coerced into an object array.
No full header/parser/elaborator or self-hosting acceptance is claimed.
