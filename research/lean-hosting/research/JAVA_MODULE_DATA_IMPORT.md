# Bounded ModuleData ingress

`java-ir-baseline/module-data-graph.clj` converts a complete source-native
`lean-module-dag/1` aggregate directly into Java PreparedGraph recipes. It does
not construct the legacy World or run import, initialization, or kernel checking.

The separate `PreparedGraph.moduleData` profile admits at most 150,000 normalized
constructor/Array nodes, one aggregate root, no globals, positive RC, closures,
Refs, ByteArrays, or signed GraphInt carriers. Existing graph profiles retain
100,000 nodes. The engine admits one ordinary companion and one module aggregate;
it refuses repeated module admissions, including in forks. Importing the module
first consumes the ordinary slot too. Both slots retain their source provenance.
This is a first bounded preloaded-module profile, not incremental module loading.
The combined import envelopes permit at most 250,000 Nodes; engine runtime work
and finalization allocations need their own measured resource acceptance.

The converter validates every record, BFS identity, tag inventory, layout,
complete part-root coverage and pinned producer source. It authenticates the
source digest before preparing recipes and again before returning them. Two
streaming passes retain immutable String/MPZ leaves by source ID, preserving
aliases; recipes retain original source IDs for all constructor/Array references.
Array size comes from its live fields, not spare native capacity. All native
constructor scalar padding is copied. Strings decode exactly `size-1` UTF-8
bytes and independently check the source codepoint count. Only MPZ values above
Long.MAX_VALUE are admitted here, with exact immutable BigInteger carriers;
negative/small MPZ require a different typed profile.

Generic immediate words are not intrinsically Nat or Int. Pinned Lean's 64-bit
Int decoder casts the unsigned payload through signed32. Every immediate above
INT_MAX therefore requires a source-bound typed-use witness. The current adapter
requires the trusted host's `:domain` proof callback to cover the exact
`[artifact-sha256 node-id field-index decimal]` slot, returning `:nat` or
`:unsigned`; absent or wrong-domain evidence stops before PreparedGraph creation.
Physical constructor tags do not count as typed proof. This callback is an
integration seam, not a public certificate or a substitute for the native typed
producer census. Bind it to authenticated paired-producer evidence before actual
artifact admission. A digest supplied by an untrusted caller establishes no
artifact authority.

`module-data-census.py` is a streaming metadata audit with a 256 MiB address-space
cap. The historical Prelude source digest
`b7944afc00bdcb3c016fd15fd2cb99c5e66dbc227659744bcf202f24d308a092`
has 22,301,185 bytes, 134,363 source records and 131,669 normalized Java Nodes:
126,724 constructors, 4,945 Arrays, 2,691 immutable Strings and three MPZ leaves.
Constructor scalar tails contain 910,232 bytes including padding. Serialized
fields contain 318,013 references and 42,900 immediates; adding the aggregate root
reference matches the producer inventory. There are 481 immediate slots above
INT_MAX. Three MPZ leaves are exactly 18,446,744,073,709,551,616. These are census
facts; the actual typed uses and paired producer artifact must be authenticated
separately. No finalizer/runtime capability is implied by the 1,188 IR entries.

Validation for the source unit: standalone Java11 compilation passed with
`javac -J-Xmx192m`. Clojure delimiter checks and `git diff --check` passed.
Focused source tests cover alias preservation, live Array size, padded scalar
tails, UTF-8, exact MPZ, digest mismatch, ambiguous immediate rejection, malformed
records, the separate bounds, second admission, and fork slot preservation.
They are registered in the combined check runner but have not yet run in this
worker: no runtime JVM, image restoration or native executable was launched.
Actual finalizer execution, source/store leases, imported kernel association,
combined heap measurement and active-association fork policy remain independent.

Retained-JVM integration subsequently exercised the structural-exporter pair
with pair-audit SHA256
`08ec92e1e5c353aa58be369a769a9740f38102601fe60e85b5868656cdc48155`.
All 2,314 imported constants matched the paired store's exact checking shape,
including types, values, binder names and binder annotations. The comparison
covered all eight ConstantInfo variants in 73 batches of at most 32; it took
3.64 seconds in an already running JVM capped at 384 MiB. This is artifact
correspondence, without proof replay or guest finalization, and is not a Lean
execution benchmark. The immutable ModuleData graph was reused between probes.

The source assembly adapter is `lean/JavaModuleImport.lean`. It uses real Lean
constructors and `finalizeImport`, under the pinned field layout, with explicit
guest-only virtual regions and no native region-address transport. Its first
runtime probe installed the aggregate and executed the actual local value action;
subsequent module-name construction stopped at the unsupported original
`Substring.Raw.Internal.isEmpty` operation. No finalized environment or imported
kernel association was issued. Failed execution unwind remains unsupported in
this profile; the memory-only failed engine was discarded rather than reported
as successfully disposed.

The next probe bound eight authenticated original Substring exports after an
exact source/ABI closure audit (138 reachable rows, no additional initialized
globals). It assembled the requested/effective imports using the original guest
constructors and ran `JavaModuleImport.finalize._boxed` to an actual `IO.ok`
environment, with the original extension callbacks enabled. Real shim helpers
reported quotient initialization enabled, a nonempty environment, and exactly
2,314 checked constants. All 2,314 constants from that **finalized checked map**
also matched the paired store's complete checking shapes, in 3.87 seconds.
The native-symbol provider explicitly reported symbols absent, selecting Lean's
interpreted initializer fallback. Heartbeats used the existing opt-in lab
allocation counter; this is not native heartbeat parity.

A pristine runtime seed fork before ModuleData installation/startup took 88 ms.
The seed and finalized child together used about 199 MiB of live heap after GC
in the retained 384 MiB JVM. This observation does not measure peak allocation,
establish production memory requirements, or authorize checked-association
forking. The next boundary is a sealed finalizer-run lineage and an owner-anchored,
artifact-relative Java kernel association; source-file checking, compilation,
project loading and program execution must then pass through that association.
