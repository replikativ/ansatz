# Original pointer-address declarations and Name comparison

Source-only fixture from Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Every selected original CAS blob
was size-bounded, SHA256 authenticated, and checked for its exact structured
Name. Only optional top-level `pretty` was removed. No JVM or pointer execution
was performed during extraction.

`original-rows.json` contains `ptrAddrUnsafe` and its genuine boxed wrapper.
The exact primitive ABI is `(erased, @&tobject) -> usize`. The wrapper accepts
two owned tobject arguments, calls the primitive, decrements the object argument,
then boxes the usize result. A direct primitive observes a borrowed input;
it does not acquire or release an object credit.

`name-comparison-rows.json` is a separate 12-row actual static FAP/PAP closure
for the private `Lean.Name.quickCmpImpl` and its boxed wrapper. Its private
component `0` is a **numeric Name segment**, not a string segment. Preserve the
record's structured Name; reconstructing it by splitting the printed label
would change identity. This closure contains the pointer primitive once, so
combined Programs should deduplicate exact Names across the two files.

The original comparison uses two pointer-address calls followed by USize equality,
returning Ordering.eq when equal. It never orders pointer addresses. Otherwise
it compares cached UInt64 Name hashes and uses genuine structural quickCmpAux
for a hash collision. Pointer ordering, native address reproduction, raw FFI,
dereferencing, native allocation identity, or parser completeness does not follow
from this fixture alone. The research engine implements the restricted
[certified identity-equality profile](../../../research/JAVA_POINTER_IDENTITY.md).

The pinned native helper literally casts the Lean object word to size_t. Native
immediate tagged values, native heap objects and Java logical carriers have
different representations; Java identityHashCode is not a collision-free address.
The runtime profile documents Nat/Int and heap-carrier ambiguities and rejects
unsupported carriers rather than claiming the native raw-address ABI.

Per-record raw identities and separately derived fixture hashes are pinned in
`provenance.edn`. Upstream copyright Microsoft Corporation and contributors;
derived material is distributed under the pinned
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
Sources: [Init.Util](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Util.lean),
[Lean.Data.Name](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Data/Name.lean),
and [lean.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h).
