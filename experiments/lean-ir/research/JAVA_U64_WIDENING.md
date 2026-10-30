# Widening supported scalar lanes to UInt64

The reached original `Lean.Level.Data.hash` body calls `UInt32.toUInt64`.
`lean_uint64_to_uint32` was already registered; it is the opposite narrowing
operation and cannot supply this binding.

Register exactly three source-adjacent supported-lane widenings:
`lean_uint8_to_uint64`, `lean_uint32_to_uint64`, and `lean_usize_to_uint64`.
Their exact original roots and boxed wrappers are in
`test/fixtures/java-u64-widen-runtime/`, authenticated against source index
`74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.
All raw parameters are owned unboxed scalars and all results are uint64.

Pinned Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, lean.h lines2045,
2119 and2205 implement the three functions as casts to uint64_t. UInt8/UInt32
zero-extend, including values with their source high bit set. USize preserves
all bits on this fixed64-bit producer profile. The existing input lanes already
validate their width; the implementation transfers their normalized long bits
into the existing UInt64 result lane. Public USize/UInt64 high bits retain their
positive BigInteger views. These explicit conversions do not make the two lanes
interchangeable elsewhere.

No public API, Node field, allocation/copy path or ownership rule changes.
The existing explicit scalar-family predicate includes the new intrinsic IDs;
no ordinal-range widening is used. Genuine boxed wrappers consume their source
boxes/immediates and allocate the normal UInt64 box. Scalar partial application
still requires those wrappers. UInt16→UInt64 exists in the pinned header but is
not enabled: its input lane remains recognized metadata without execution
support. No new UInt16 lane or unrelated narrowing conversion is added.

The fixture's tiny native oracle compiles the three verbatim pinned inline bodies
with attributed Apache 2.0 source/license, fixed64-bit size assertion and typed
input scaffolding. It checks fifteen source-width boundary vectors, including
UInt32 2^31/2^32−1 and USize 2^63/2^64−1. The bounded native run exited0 with
empty stderr under a 256 MiB address-space cap. It is an arithmetic/cast oracle,
not a full Lean runtime ABI, captured state or frontend-completion proof.

`u64-widen-checks.clj` provides five focused tests for both drivers. The root will
run them in its retained REPL using the new isolated jar, then retry the genuine
original frontend boundary and perform integration gates. No additional Clojure
runtime or frontend image is launched by this feature worker.
