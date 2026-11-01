# Hosted Lean memory investigation, 2026-10-24

Research evidence, not a shipped memory requirement. Earlier interrupted runs
and subsequent public-loader acceptance are distinguished below.
This updates the [campaign continuation](CAMPAIGN_CONTINUATION_2026-10-23.md).

Subsequent integration update: [public single-file P1 now passes](../measurements/public-project-p1.json)
with scoped projection and a 3 GiB heap. All 65,994 Init constants were freshly
checked, public loading/calls completed, and all 2,151 pins matched after
disposal. This changes the campaign status, not the scope of earlier measurements
below. It does not isolate scratch savings, establish 2 GiB fit or prove native
reset/P2 or production memory behavior.

## Where PR 153 leaves file loading

PR 153 merged the compact first-pass dependency plan and continuation/release
research. Its focused regression passed 22 tests and 235 assertions. It does not
complete public Project `load-file` acceptance. Earlier resident experiments
genuinely compiled source, imported original/edited macros, retained old versions,
called Nat/Unicode exports and invoked typed Clojure callbacks. The public
orchestrator still needed genuine end-to-end acceptance at that historical point.

The newly selected consumer passed host construction with 257 selected runtime
rows and three caller rows. Selection and construction do not themselves prove
restoration, fresh checking or source-file calls.

## Actual full restoration with a 2 GiB heap

The v5 experiment used a 2,048 MiB JVM heap, 3,072 MiB process-group RSS cap,
4,096 MiB launch-available threshold, unchanged 1,024 MiB available-memory floor,
and 5,400-second wall cap. It preserved the strict checking and guest execution
policies; no kernel verdict, ownership requirement or initialization step was
omitted. Earlier launch refusals did not execute a Lean JVM.

The frontend **restored successfully**: 334,467 functions, 776,060 local heap
entries, 56,125 globals and 6,968 preserved initialization guards. Restoration
completion was first observed 767.7 seconds after the first monitor sample;
this is an observation interval, not an isolated restore benchmark.

Fresh Java projection subsequently reached 2,048 of 65,994 constants. In a recent
124.76-second observation window, GC counters advanced about 118.14 seconds.
The operator stopped the run for sustained GC pressure. Elapsed guarded lifetime
was 1,703.72 seconds; peak process-group RSS was 2,528,686,080 bytes; minimum
available system memory was 1,296,498,688 bytes. Neither the RSS cap nor the
available-memory floor triggered this stop.

The guard disposed its process group and all 1,268 input hashes matched afterward.
This is a resource-stopped run, not a logical kernel rejection. It issued no
public loaded Project, FileHandle or export call. Process disposal does not prove
that guest Source.close ran. The evidence does not establish a minimum viable
heap, nor that a representation change will make the whole check fit in 2 GiB.

Evidence directory: `target/artifact-contract/compact-init-p1-2048m-v5/` in the
compact-init-check-plan worktree. Plan SHA-256:
`9a578fd5a09748bafc45d081d3f9579648319ffd82ffa7f73795f45c178f61a2`.
Receipt SHA-256:
`5157f6f0e63b8accf2108a6c1cbc2912e47ba7618638a769731fc704d72e89f2`.

## Representations and measured small experiments

The source's 11,233,359 native nodes already live in a disk-backed store. They
must not be counted as resident Java objects. The store uses bounded decoded-row
caching; file/page cache and JVM live heap are different quantities. Function
registries also share the same parsed function objects rather than copying each
body three times.

A restore-scoped `[:var Long]` sharing prototype reduced distinct leaf identities
from 1,053 to 81 in 127 sampled function rows and from 20,480 to four in a synthetic
packet. Checkpoint bytes and three-backend results were preserved. However, its
additional rewrite pass used about 3.6 times the allocation and 7.6 times the time
of synthetic baseline admission. It was **not adopted**. No retained-byte or
whole-archive savings measurement was made.

An opt-in cold-code prototype stores function bodies as independently hashed
file rows behind stable persistent-vector root views. Ordinary eager function
maps can keep their identity across world/prepared registries and forks; nested
code is ordinary data when materialized. A bounded run passed 457 checks,
including exact wire preservation for 127 sampled functions, vector operations,
metadata/scalar handling, eviction, byte corruption/truncation, close behavior
and old/cold/old execution on reference, mutable and JVM backends. Its v2 run took 5.77
seconds at a 256 MiB heap and 386,535,424-byte peak group RSS. After failure-path
file cleanup was hardened, the same checks passed in 7.81 seconds at
379,506,688-byte peak group RSS, with all 268 input hashes matching afterward.
See the [scalar evidence](../measurements/compact-host-memory.json). The NaN fixture
uses wire preservation; ordinary numeric equality is unsuitable for that case.

This only establishes sample compatibility. Its advisory cache limits encoded
bytes and entry count, not decoded heap bytes. It is outside the admitted runtime
profile. Production integration still needs explicit entry materialization,
validated immutable width proofs, independent source reconstruction and
authorization, shared resource leases and compiler-cache retention analysis.
The sample does not establish retained-byte savings or full-frontend performance.

## Next bounded change and remaining sequence

The strict projection memo retains temporary `:names`/`:levels` linked lists and
`:constant-val` maps after Java constants and expressions have copied the needed
fields into arrays. A conservative experiment can put these kinds in a separate
scratch memo, reuse them while constructing one complete ConstantInfo, and then
drop that scratch memo. Preserve global expression, name and level DAG sharing,
failure/cycle behavior and every fresh checking rule. Do not scan the growing
global table per constant or clear the process-wide Name interning table.

The opt-in split-memo prototype passed four tests and 425 assertions, including
all eight ConstantInfo variants from the checked-in native-produced fixture,
exact checking shapes, cross-release expression identity, full-width/fallback
keys and failure/cycle recovery. Its 256 MiB run took 3.87 seconds at
381,747,200-byte peak group RSS; all 269 inputs matched afterward and the process
was disposed. No fresh Java kernel admission or full Init projection ran.

In a synthetic 24-group workload with 48-element name/level lists, the baseline
memo held 2,338 entries at completion; the split version held eight persistent
entries and zero scratch entries after release. Five alternating paired trials
gave median allocated bytes of 3,869,952 versus 5,076,768, and median elapsed
times of 7.46 versus 11.48 milliseconds. Only the split candidate includes
per-lookup/per-kind diagnostic counters and additional metrics maps in these
intervals; the baseline is uninstrumented. Thus this instrumented prototype traded
less memo retention for about 31% more allocation and 54% more time. Name interning
remained at 87 entries throughout those trials. These are table/allocation
measurements, not retained-byte savings or a representative full-corpus speed
comparison, and do not isolate the cost of the scratch-lifetime policy itself.
At that measurement point the admitted memo/profile remained unchanged. Integration required exact
fresh Java admission parity and a wrapper enforcing complete-constant scratch
lifetime, rather than caller discipline alone.

## Scoped projection integration candidate

The compact verifier now uses a whole-ConstantInfo wrapper. It keeps `:expr`,
`:name`, `:level` and other core memo entries shared for the complete projection,
while `:constant-val`, `:names` and `:levels` use scratch tables. A completed
constant has already copied those temporary maps/list fields into its Java
fields and arrays. The wrapper retires scratch on both success and failure;
there is no public intercomponent clear operation or global-table retirement
scan. Retirement sets the scratch slot to nil without allocating. A later scratch
access recreates the tables under the existing lock. Foreign worlds and complete
operation reentry are rejected before envelope reads or scratch retirement.

The original `make-projector` bulk API retains its cumulative semantics. New
`make-scoped-projector` returns component inspection and complete-constant
projection operations. Existing layout, typed-key, world identity, cycle,
ownership, policy and fresh Java admission checks remain in place. Successful
children survive ordinary projection failures. If exceptional cleanup itself
fails under resource exhaustion, the original Throwable is propagated rather
than masked; projector reuse after such failed cleanup is not promised.

Focused tests cover all eight native-produced variants, complete native
17-constant fresh checking in both input orders, exact environment/checking
shapes/order/policy, closed ill-typed declarations rejected by the actual checker,
stable core identities, bounded scratch retention across distinct rows, cycles,
foreign malformed-world rejection and allocation-free failure retirement.
Focused integration validation passed **36 tests / 22,518 assertions**, with
zero failures/errors, including freshly compiled current Java classes and the
public compact verifier's strict native-fixture admission. The serial compile/test
run took **7.885 seconds**, with **454,602,752-byte** peak process-group RSS under
a 384 MiB test heap and 768 MiB RSS cap. All **271** source/jar/fixture inputs and
**48** fresh class outputs matched afterward; both process groups were absent.
The first run had one test-only expected-exception capture error (Java rejects
with RuntimeException, while the old fixture helper catches ExceptionInfo); the
checker correctly rejected the invalid declaration. The corrected test preserves
the expected strict rejection/message. See the [validation record](../measurements/scoped-kernel-projection.json).
No full Init projection, retained-heap comparison or genuine P1 passed for this
change. These tests do not establish that scratch retirement makes it fit in
2 GiB, and further full attempts require an explicit resource envelope.

The preceding full P1 run using the shared-IR restorer/runtime
`253d`/`c32` restored the full frontend but was interrupted during fresh projection
at **33,792 / 65,994** constants after **662.654191 seconds**. Peak process-group
RSS was **2,537,594,880 bytes**, minimum available system memory was
**1,984,000,000 bytes**, and post-full-GC live heap approached **1,995 MiB** under
the 2 GiB heap, with roughly 300 full collections. All **1,858** pinned inputs
matched after process disposal. This is neither a strict-check pass nor a public
file-load pass. Evidence: `shared-ir-c32-p1-2048m-v1/run-v1/receipt.json` and
`postcheck.json` under the campaign's `target/artifact-contract` directory.

Scratch retirement does not eliminate the final Java Expr DAG, core typed memo,
guest heap or eager code baseline. Small-sample reductions must not be
extrapolated to the full frontend. Native ModuleStore objects already live on
disk behind a bounded decoded-node cache. `ExprStore.resolve` reconstructs entire
expression subtrees; it is not a drop-in bound while all ConstantInfos remain
strongly retained. Global Name interning (`Name.java`'s strong static map) also
needs a separate future warm-session/edit/close lifetime measurement and identity
contract review before any weak-interning change. None is included here.

Separately, a fresh native-only D oracle on pinned Lean 4.33.1 observed an empty
initializer action list, direct Init imports with meta false/true, and three
local declarations: borrowed-Nat `D.nat` adding 100, its owned boxed wrapper, and
String self-append. It completed in 0.547 seconds with 286,900,224-byte peak RSS;
all 64 inputs matched and the process was disposed. This supports only the
initializer-free P2 fixture, not hosted/P1/P2 acceptance. Evidence:
`p2-native-D-oracle-v8-taskmanager1/run-v1/inventory.json` in the same campaign
artifact directory.

Run bounded semantic and memory controls before selecting a new consumer or
repeating the expensive full run. Counts alone do not measure retained bytes.
The existing dependency planner runs after this stalled projection phase, so
another planner change cannot explain or resolve this particular observed peak.

The campaign order remains:

1. Complete genuine public single-file loading, issued handle/version, Nat and
   Unicode calls, cleanup and postcheck.
2. Exercise independent-root projects, native reset, reload and retained versions.
   The prepared P2 draft is definitions-only and remains gated by actual P1.
3. Establish Project-level bidirectional interop, then explicit IO capabilities.
4. Consolidate measured runtime performance, Init/store profiles and release
   packaging with accurately stated support and limits.

Do not raise the heap repeatedly as a substitute for isolating the representation
and checking peaks. LLVM and the independent Pattern/Raster work remain optional.
