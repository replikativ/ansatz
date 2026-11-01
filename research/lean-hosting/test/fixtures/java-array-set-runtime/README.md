# Original checked array update

Two exact original declarations from accepted producer index `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`: `Array.set!` and its unchanged owning `_boxed` wrapper. Each record retains its original raw CAS SHA; only top-level `pretty` was removed. `provenance.edn` pins the transformed fixture and full pinned upstream source bytes. Upstream Lean source is Apache 2.0; see `LICENSE`.

Pinned Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).

The native extern has four parameters: erased type, owned array, borrowed Nat index, owned replacement; result is an owned array. There is no proof parameter. The real boxed wrapper owns its Nat parameter and performs its original decrement after the native call.

`Init/Data/Array/Set.lean` supplies a total pure fallback, but native `lean_array_set` in `lean.h` checks logical bounds and calls `lean_array_set_panic` on failure. `object.cpp` releases the replacement and calls the panic handler with the array as default. The Java bounded profile supports the valid in-bounds path and explicitly rejects this panic policy before native primitive effects; it does not claim the fallback's unchanged-array result or native panic output/continuation behavior.
