# Scalar and buffer construction checkpoint

`scalar_buffer_checks.clj` uses host values and explicitly labelled structural models. `ManagedScalarBufferChecks.java` exercises the actual compiled engine using synthetic minimal declarations, including execution of four exact-ABI numeric externs. Neither test issues native source evidence or substitutes for the native application acceptance gate.

The trusted planning algebra extends the existing constructor recipe:

- `{:tag t :fields [...]}` or `{:kind :constructor :tag t :fields [...]}`: existing object-only constructor.
- `{:kind :scalar :lane "uint64"|"usize"|"float"|"float32" :bits Long}`: exact raw bits, materialized through `DataCtor.boxedScalar(String,long)`.
- `{:kind :array :fields [...]}`: live elements, materialized through `DataCtor.array(Object[])`.
- `{:kind :bytes :bytes byte[]}`: a private caller snapshot, materialized through `DataCtor.bytes(byte[])`.
- `{:ref index}`: an earlier recipe, represented internally by `DataRef`.

Every recipe must have exactly one incoming parent or root occurrence. All mutable recipe arrays are bounded and snapshotted inside `constructDataArguments` before allocating guest Nodes. A recipe never accepts a live guest Node. The engine creates the existing scalar BOX layout, Array tag 246/ArrayState, and ByteArray tag 248/ByteArrayState. Ordinary constructors remain compatible. Empty arrays and byte arrays are special managed Nodes; empty ordinary constructors remain immediate tags.

The existing 100,000 field/root occurrences, 4,194,304 aggregate integer bits, and 1,048,576 aggregate String units remain. Aggregate managed scalar/buffer payload is additionally capped at 1,048,576 bytes. Host buffer codecs cap byte results/inputs at 1 MiB and array elements at 100,000. Recursive planner/decoder aggregate and cycle limits remain the caller's responsibility.

`ansatz.lean.jvm.scalar-buffer` exposes type-directed pure planning and borrowed decoding helpers. Machine integers/words return exact `BigInteger`; signed values range-check before two's-complement encoding. UInt8/16/32 and Char object-lane values are immediate unsigned Longs; 64-bit/word/float values use recipes for managed scalar boxes. Float32 takes/returns exact `Float`, Float takes/returns exact `Double`; encoding uses raw bits. Char takes an integer Unicode scalar code point and returns `Integer`; surrogates and values above U+10FFFF are rejected. Bytes require an exact `byte[]`; arrays accept bounded exact `Object[]` or indexed Java Lists, snapshotting before engine allocation.

`decode-scalar` is for object lanes; `decode-raw-scalar` takes an exact Long bit word after the caller normalizes the actual scalar result lane. `decode-bytes` copies the live extent. `decode-array-fields` is an internal borrowed field snapshot for recursive decoding, not a public result and not new ownership. Caller must retain the actual owned root throughout decoding, then release only that root using the existing journal. No helper acquires guest credits, changes globals, imports a graph, starts tasks, or admits host IO.

Numeric runtime expansion is limited to the observed exact externs: `lean_uint8_add` (modulo 256), `lean_int64_neg` (existing UInt64 two's-complement negation), `lean_float_add`, and `lean_float32_add`. Their scalar parameter/result ABIs require all borrow flags false. Three new semantic IDs are positively classified; Int64 negation reuses the existing audited `U64_NEG` ID. Other numeric symbols remain subject to existing rejection.

## Float32 literal dependency follow-up

Five additional exact externs are implemented because actual captured Float32 literal declarations depend on them. All parameters have the captured `borrow=false` ABI: `lean_float32_of_bits : uint32 → float32`, `lean_uint32_of_nat_mk : tobject → uint32`, `lean_float32_div` / `lean_float32_mul : float32 → float32 → float32`, and `lean_uint64_to_float32 : uint64 → float32`. No adjacent family members are registered implicitly.

At pinned Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, the operative native definitions are `src/include/lean/lean.h:2090` (consuming Nat narrowing), `:3256` / `:3257` (float32 multiplication/division), `:3265` (direct unsigned64-to-float conversion), and `src/runtime/object.cpp:1987` (Float32.ofBits). The pin contains no `src/runtime/numerics.cpp`; the definitions above are authoritative. `ofBits` canonicalizes NaNs, unlike raw host codec bit transfer, while preserving non-NaN bit patterns. This matches existing Float.ofBits behavior.

The standalone tests execute every added primitive, including modulo narrowing of a large Nat, subnormal/tie rounding, signed zero/infinities, overflow and NaNs. A UInt64 value `2^63 + 2^39 + 1` must convert directly to Float32 bits `0x5f000001`; an incorrect intermediate Double rounds the integer down to the midpoint and then produces `0x5f000000`. The engine uses `BigInteger.floatValue()` on the exact unsigned integer to avoid that double rounding. The SDK launcher compiles and executes these checks; native application acceptance is a separate gate.
