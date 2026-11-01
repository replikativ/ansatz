# Lazy field storage in mutable execution

The first three observed normal full-Init callbacks spent 906–1046 ms in two
`mutable/thaw` calls per callback, versus 77–93 ms in two freezes. The first
callback (`convTactic`, 508,909 local heap nodes) spent 906.5 ms thawing and
77.2 ms freezing within a 2913 ms handler. These observations justify removing
unused eager field copies; post-adoption timings remain to be measured.

Previously thaw allocated an updated node map and an `Object[]` for every local
node with positive RC, even when execution only read it or changed its RC.
Thaw now shares immutable node maps and vector fields for all RC values. It
still copies every nonvector field collection, including externally supplied
RC0 arrays, so writable arrays never cross machine boundaries.

Only constructor field stores and exclusive array element stores acquire an
owned `Object[]` on first write. Validation precedes materialization. Array
stores use the current node after releasing the old element, preserving any RC
changes and all other node metadata. The storage copy performs no guest retain
or release. Repeated stores reuse the owned array and always mark the node dirty.

RC updates, tag updates and scalar-byte updates continue to replace immutable
node maps, retaining their existing immutable fields. Scalar bytes remain
immutable maps; scalar writes do not require an object-field copy. New guest
allocations and generic node replacement retain their existing eager private
array behavior. Persistent refs and tasks still update through node replacement;
this change does not make RC0 resources read-only. Imported NativeSource nodes
remain immutable and cannot enter either local in-place write path.

Freeze still clones every owned array before exposing vector fields. Thus a
snapshot remains unchanged if its parent machine later writes again, and two
machines thawed from the same unique guest reference can mutate independently.
Immutable vectors can be shared through both delta and full freezes.

At this field-only stage, thaw still created a Java HashMap entry for every
local heap node, plus register, frame, global and other execution-state storage.
The change removed eager field-array/node-map copies without changing guest
exclusivity, ownership, allocation counters or instruction fuel. The later
overlay stage below removes the full heap-map copy as well.

`prototype.mutable-field-cow-test` covers unchanged storage across reads and
RC/tag/scalar updates, one-time private storage acquisition, continued parent
writes after freeze, independently mutated forks, RC2→RC1 transitions, rejected
writes, nonvector RC0 inputs, exact child release/events and persistent ref/task
replacement. Existing mutable, array, scalar, task and persistent-snapshot tests
supply broader semantic and snapshot coverage. Focused validation is coordinated
separately under the campaign memory guard; no live adoption is implied here.


The final focused run passed 47 tests and 1,985 assertions with no failures or
errors under a 256 MiB heap limit. The memory guard observed at least
2,045,264 KiB available system memory. Review additionally required converted
nonvector nodes to be marked dirty during the existing thaw pass, so a no-write
freeze cannot return externally mutable input arrays. The regression freezes
before mutating the caller's array and checks both snapshots and machines.


Live adoption at the unexecuted outer callback at 393,997,331 guest steps
preserved the Machine class and runtime sentinel identities. A tiny two-fork
canary passed before resumption. The first three resumed callbacks returned
normally, but total thaw time was still approximately 0.9–1.3 seconds for two
thaws over about 515,000 nodes. These were different inputs under changing
memory/GC conditions, immediately after function refresh; they establish no
wall-clock speedup. Further bounded profiling will distinguish register sizing
from the remaining heap-map copy. See
[the first post-change observations](../measurements/hosted-eval-const-field-cow-phases.json).

A full regression attempt with the import paused reached the IR-value tests,
then its own process was stopped by the 1 GiB system-memory guard. It did not
complete and is not a passing full-suite result. The focused result above is
separate. The guard did not interrupt the frontend REPL.


## Persistent-base writable overlay

Three later observations separated the remaining costs: two heap-map thaws
cost 568–698 ms, while register sizing cost only 0.08–0.14 ms. The actual heap
contained about 525,000 nodes. See
[the nested timing record](../measurements/hosted-eval-const-thaw-detail-phases.json).

`ansatz.runtime.HeapOverlay` now holds one persistent snapshot base, private
writes and deletion markers, and an effective size. It implements `Map` through
`AbstractMap`; live views and default mutations participate in dirty tracking.
It never borrows another mutable overlay as its base. Existing dirty-delta
freeze publishes ordinary persistent maps, cloning owned field arrays as before.
Only heap type hints changed to `Map`; frame joins and globals still use HashMap.

Thaw still scans the input once to normalize caller-owned nonvector fields and
validate the allocation-free Long-key lookup profile. This is not O(1) thaw.
Canonical nodes create no new heap-map entries. The common lookup path requires
Long keys and an exact PersistentHashMap or PersistentArrayMap base; generic
maps verify the stored key to preserve the former Java HashMap key equality.
This avoids mixing Clojure numeric-key equivalence with Java key equality.

The overlay plus a JVM-only String type hint in numeric primitive dispatch
passed 90 focused tests / 4,366 assertions, then the full JVM suite passed
641 tests / 39,629 assertions, with no failures or errors. Javac compiled the
new class; tests ran with a 256 MiB heap and the unchanged 1 GiB system-memory
floor. The full run observed at least 1,616,884 KiB available memory.

Live adoption at the unexecuted outer callback at 432,619,707 steps preserved
the Machine class and sentinel identities and passed a two-fork canary. The
first three normal callbacks after resumption thawed a larger, approximately
738,000-node heap in 123–135 ms per thaw. Each happened to need one thaw rather
than the preceding samples' two, so whole-callback times are not a paired
comparison. These are diagnostic observations, not a competitive benchmark.
See [the overlay observations](../measurements/hosted-eval-const-heap-overlay-phases.json).


A later 20-second profile still attributed many allocations to register arrays.
The numeric helper's prefix checks now compile to direct JVM String calls; the
remaining suffix checks in `runtime-prim/evaluate` received the same JVM-only
hint after 35 focused tests / 2,296 assertions passed. Live recompilation emitted
no reflection warnings (two unrelated primitive-loop boxing warnings remain).
The full 641-test result predates this second receiver hint; its separate
focused result is recorded in `measurements/frontend-progress.json`.
Allocation weights are estimates; both recorded profiles report the first sample
separately because the initial recording contained an extreme outlier. No exact
allocation total or phase-to-phase speedup is inferred from those weights.
