# Globals boundary experiment

The [actual frontend CPU profile](../measurements/resident-import-cpu-profile.json)
finds 288 samples nearest globals reconstruction in `freeze` and 145 nearest
copying globals in `thaw`. These are observed source frames, not self time. This
experiment changes only the mutable globals storage at those boundaries.

The first candidate borrows a validated ordinary immutable globals map for reads.
Its first mutation, unsupported-key lookup or request for a mutable view creates the original eager
HashMap representation. An unchanged eligible map can be reused when freezing;
a changed map follows the existing full persistent-map reconstruction. Sparse
write freezing, slot-width caches and runtime adapter changes remain separate
experiments.

Eligibility must preserve the original Java HashMap key relation. It is cached
by weak map identity and admits only explicitly supported immutable keys/maps.
Unsupported maps and maps with metadata retain eager copying. Read-only reuse
preserves abstract map contents/equality; concrete map class, identity and
iteration order are storage details. Metadata follows the previous conversion
behavior. Key walks have a 4,096-node work/queue bound, and the weak identity
hint cache retains at most 256 entries. Unsupported maps retain eager copying. Mutation materializes before applying
unsupported keys, preserving the previous HashMap behavior when Java-distinct
keys become equivalent during later Clojure map reconstruction. No guest
retain/release or initializer operations belong in the storage helper. Successful
materialization releases the helper's borrowed base references; it does not retain
a second full table for the remaining lifetime of a changed machine.

The external world still carries a persistent `:globals` map. Tests must cover
snapshot/fork isolation, initialization pauses, recursive initialization, IO
success/failure, persistent closures/native references, Integer/Long and nested
numeric keys, null, comparator maps, mutable maps and live Java views/default
mutators. The ordinary interpreter and compiled execution backends supply
behavioral comparisons.

The bounded benchmark uses the exact same script in the archived and candidate
worktrees: ten warmup operations, five samples of five independent operations,
0/56,125/100,000 synthetic globals, and unchanged, eight-instruction call,
one-write and thousand-write cases. Writes manipulate Map storage directly;
regressions separately establish guest semantics. These timings exclude hosted
frontend work and do not establish its speedup.

## Authenticated runtime boundary

The archived producer remains unchanged in its original worktree. A changed
interpreter is a new consumer build even when snapshot shape is unchanged.
The existing factory requires matching producer/preparation/loaded identities,
so its old checkpoint cannot silently be reused with this implementation.

A later explicit compatibility consumer should record the immutable producer
identity, the actual loaded consumer inventory and an allowlisted compatibility
decision, retain checkpoint/artifact authentication, recreate bindings through
the reviewed consumer and obtain fresh checking authority. The bounded tests and
synthetic benchmark here do not establish that compatibility or actual frontend
performance. No manifest, checking association or binding identity is relabeled.


Run Java compilation from the worktree root with `clojure -J-Xmx512m -T:build javac`.
Then, from `experiments/lean-ir`, run
`clojure -J-Xmx512m -M scripts/globals-boundary-benchmark.clj`.
Use the same script bytes with the baseline revision for comparison. Its fixed
case order and small sample count permit JIT/order/GC effects, particularly for
sub-millisecond results; retain raw samples and avoid extrapolating a precise
speedup to frontend compilation.

## Next authenticated execution gate

Review of the original factory establishes that `:implementation-sha256` means
its complete loaded host implementation inventory. The optimized factory must
not return the producer's `50f...` identity under that old contract. Introduce a
new restore-consumer API whose receipt separates `:producer-preparation`,
`:consumer-implementation-sha256` and a closed `:compatibility-profile` such as
`"globals-first-mutation/1"`.

The profile pins the archived producer, recipe, resolver and external manifest;
allows exactly the changed `mutable.clj` and new `GlobalsOverlay.java`, outer
class and nested `GlobalsOverlay$Hint.class`; and separately pins the new factory,
consumer and launcher. All other inventoried source/classes, guest code,
executable reconstruction, binding authority, trusted roots and kernel policy
must match. Preserve resource acquisition/cleanup and authorization checks.
The restored result remains `:restored-precheck` with `:strictly-checked? false`.

Keep the old restorer unchanged. A reviewed experimental copy with an explicit
identity-check revision is preferable to altering the meaning of its old fields.
Reject wrong producer/recipe, unlisted source or class changes, missing/shadowed
nested classes, changed bindings/roots/policy and failures after resource
acquisition. Then run the small authenticated checkpoint before repeating the
full public workflow and fresh checking. This changes the consumer API/profile,
not checkpoint wire data, and need not repeat the entire Init bootstrap/finalization.


Eligibility hints are internal derived-map storage attestations, not checking or
binding authority. `rememberSnapshot` supports only the actual frozen result of
the same machine; arbitrary host cache admission is outside its supported API.
The [validation receipt](../measurements/globals-boundary-optimization.json)
records source pins, checks and every measured attempt separately.

## Measured candidate

Final Java compilation and focused checks pass (25 tests / 893 assertions).
The complete prototype passes 835 tests / 89,256 assertions. Both the normal
library suite and built-JAR suite pass 822 tests / 3,588 assertions with isolated
stores, localhost fixture access and 1,536 MiB heaps. Earlier read-only-store,
HTTP sandbox/offline-setting and 768 MiB omega heap failures remain in the
receipt; no assertion was weakened. Optional Mathlib and missing full-Init test
fixtures are not covered by these isolated runs.

The final boundary benchmark uses identical script bytes in both worktrees:

| Globals | Operation | Baseline median ms | Candidate median ms |
| ---: | --- | ---: | ---: |
| 56,125 | Unchanged thaw/freeze | 33.932 | 0.070 |
| 56,125 | Eight-instruction call | 31.905 | 0.126 |
| 56,125 | One write | 33.067 | 40.117 |
| 56,125 | Thousand writes | 43.717 | 35.503 |
| 100,000 | Unchanged thaw/freeze | 76.751 | 0.026 |
| 100,000 | Eight-instruction call | 78.605 | 0.057 |
| 100,000 | One write | 77.330 | 74.865 |
| 100,000 | Thousand writes | 78.790 | 73.862 |

These are synthetic warm boundaries, not hosted frontend timings. First writes
still pay the old full copying/reconstruction cost, with extra wrapper/key-proof
work. The 56,125-entry one-write sample is slower; this small fixed-order run
cannot establish a precise write-side regression or benefit. Sub-millisecond
results also vary with JVM tiering/order. Cold eligibility scans are excluded.
The first candidate run predates conservative putAll/key-walk hardening; the
receipt distinguishes it from the rebuilt final code and final measurement.


The separate ready-global benchmark uses `initialized-value` in the same
optimized JVM with eager HashMap, borrowed and materialized representations.
Ten warmups of 200,000 reads precede five measured samples per case. At 56,125
globals, helper-plus-loop medians are 69.1 ns eager, 259.5 ns borrowed and 71.1 ns
materialized; at 100,000 they are 68.1, 159.1 and 65.2 ns. Borrowing adds real
per-read work even as it removes boundary copies. This is not an exact comparison
against separately compiled old code, and JVM/fixed-order effects remain visible.
It supports measuring the actual frontend before adopting the candidate broadly.
An eventual profiling policy could choose materialization for long read-heavy
segments; this experiment implements no adaptive threshold or new global cache.
