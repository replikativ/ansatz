# UInt32 and USize on the Java research engine

This extends the [captured extern runtime](JAVA_EXTERN_RUNTIME.md). The fixed
guest profile is 64-bit little-endian Lean 4.33.1, producer
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. It adds no IO, persistence or
hosted source-loading acceptance.

## Values and ownership

U8/U32/USize have distinct prepared types and share the primitive `long[]`
stack. UInt32 uses the unsigned low32 domain; USize keeps raw64 bits. Typed host
inputs are exact nonnegative integral Java carriers through the type's maximum.
Negative Long is not an ambiguous unsigned input convention. Host USize results
use Long below 2^63 and positive BigInteger above it. Guest calls keep raw bits.

Boxed U32 is an immediate, following 64-bit `lean_box_uint32`. Boxed USize is
a tag0 node with zero object fields and eight scalar bytes, following
`lean_box_usize`. Closure application boxes primitive returns using those rules;
typed roots use mathematical carriers. Caches retain raw scalar bits or owned
boxed nodes according to the result lane.

Constructors allocate `8*usizeCount + scalarBytes` bytes after object fields.
`uproj`/`uset` raw word indices include those object fields: their byte offset is
`8*(index-objectFieldCount)`. U32 `sproj`/`sset` retain an additional byte offset.
Payload bounds are checked; stores still require guest RC1. RC1 alone does not
make mutable storage private to a retained snapshot.

Seven original declarations now execute: both `USize.ofNat` signatures,
`USize.repr`, `UInt32.toNat`, `UInt32.decEq`, `UInt32.decLe`, and
`System.Platform.getNumBits`. Natural-to-USize conversion wraps low64; rendering
uses unsigned decimal; platform bits returns Nat64 for the declared profile.

Two raw-IR limits remain deliberate. Numeric literals must already fit their
unsigned width, preserving the existing U8 admission policy. Conversion externs
perform specified wrapping. USize `case` values above UInt32 maximum trap:
pinned C++ `ir_interpreter.cpp` converts its case tag to `unsigned`, while LLVM
compares full width. The engine does not choose an implicit behavior for that
divergent domain. U32 and narrower USize cases are supported.

## Evidence and next work

[ScalarOracle.lean](java-ir-baseline/ScalarOracle.lean) produced 75 native
observations: 11 USize conversions/renderings through large Nats and 64 UInt32
comparison/conversion combinations. The
[oracle receipt](../measurements/java-ir-scalar-oracle.edn) pins source bytes,
producer and values. Native externs remain enabled in IR-preferred mode.

Both Java drivers compare direct calls and guest FAP wrappers. A guest
Nat→USize→String pipeline tests high raw bits without host conversion.
Additional cases cover mixed object/two-word/U32/byte payloads, ownership,
scalar/boxed caches, AP boxing, 10,001 tail calls, mixed-lane joins, atomic input
rejection, literal limits and payload bounds. The isolated jar gate passes
54 executions / 3,776 assertions in a 384 MiB JVM.

The [receipt](../measurements/java-ir-scalars-2026-10-28.edn) records paired
warmed controls against the eight-Nat engine. The final engine prepares scalar
literal words once, rather than converting them during execution. Final
RBMap1000/1001 CPU medians were recursive 3.093/2.826 ms and explicit
4.231/4.263 ms (old/new), with equal allocation, about 1.516 MB/run. This sample
is about 9% faster recursively and about 1% slower explicitly. The earlier
pre-staging control is preserved separately; JVM histories differ, so the
between-session difference cannot be attributed entirely to staging. No separate
local test JVM overlapped either control. Shared-machine/JVM effects limit an
overall performance conclusion.

Load [compare-repl.clj](java-ir-baseline/compare-repl.clj) after the existing
REPL adapter and call `java-ir-comparison/compare-engines` with old/new
`class-basis` values to reproduce the paired check without Init loading.

RBMap main has 11 unsupported extern declarations left, down from 18. Its static
closure is complete, but execution still needs strings, arrays, valid guest
stdout and an explicit panic policy. UInt16/UInt64/floats and arbitrary native
extensions remain outside this profile.
