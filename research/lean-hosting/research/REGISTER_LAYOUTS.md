# Function-local register sizing

Implemented, focused-tested, and adopted in the live prototype with a
correctness canary. The implementation changes callee storage capacity without changing
register IDs, guest instructions, ownership, or snapshots. There is no measured
paired performance benchmark for the new policy. Later restoration/storage
adoptions below record exact state and operation counts, not a speed ratio.

The later [ordinary-macro recording](../measurements/hosted-ordinary-macro-allocation-profile.json)
justified implementing this proposal: `Arrays.fill` and `mutable/registers`
accounted for 578 of 1,654 CPU top-frame samples (about 35%). Register allocation
had approximately 10.5 GB of sampled weight, excluding the separately reported
first allocation event weighted at 188,249,522,496 bytes. These are diagnostic
samples, not exact byte totals or a comparison of runtimes. The earlier evidence
below is retained as context; the recordings cover different phases.

The [20-second post-overlay profile](../measurements/hosted-overlay-allocation-profile.json)
contains 151 `Arrays.fill` and 64 `mutable/registers` top-frame samples out of
1,805 execution samples, about 12% combined. Its sampled allocation weights
attribute approximately 4.6 GB to `mutable/registers`, after excluding the first
allocation event. These are sampling estimates, not exact allocation totals,
rates, or a benchmark. Different phases and inputs prevent interpreting changes
from an earlier recording as a speed comparison.

Extreme first allocation events are reported separately and excluded from the
weighted aggregates. The post-overlay recording reports a first `Object[]`
sample weighted at 57,848,060,864 bytes; the
[earlier recording](../measurements/hosted-runtime-allocation-profile.json)
reports a first `java.lang.reflect.Method` sample weighted at 462,158,706,528
bytes. Neither weight establishes that amount was allocated during its recording;
no cause for these extreme samples is asserted here.

The post-overlay recording also predates the completed JVM-only String receiver
hints in `runtime-prim/numeric` and `runtime-prim/evaluate`. Subsequent focused
validation passed 35 tests and 2,296 assertions, with no reflection warnings and
two ordinary boxing warnings. That validation concerns the hints, not the
register-sizing proposal.

Before this change, in the reviewed [mutable runtime](../src/prototype/mutable.clj), `thaw` derives a
program-wide register count. `call-values!` defaulted to that count when no
explicit register layout existed, and a tail transfer reused an array whenever it
was large enough. The [demand JVM runtime](../src/prototype/lazy_runtime.clj)
clears explicit layouts. Consequently, an unrelated function requiring register
4010 can give small callees 4,011-element arrays, and tail transfers retain that
capacity. Merely changing the requested callee width would not shrink them.

The [slot-count implementation](../src/prototype/slot_count.clj) already has a
private weak identity cache of individual function sizes, populated during
normal program sizing. Before this change, public `mutable/function-slots` instead
measured a one-function program through a fresh cache. It now delegates to the
validated single-function cache API. The
[eager compiler](../src/prototype/block_compile.clj) supports explicit compact
layouts using that public helper.

The implementation follows these constraints:

1. Expose a validated single-function sizing API backed by the existing weak
   function identity cache. Preserve the immutable function-map, parameter-vector,
   body-vector, and nested collection guards. Do not cache mutable or array-backed
   code. Function identity, rather than its name or structural hash, determines
   reuse: aliases may share a size; a replacement definition under the same name
   must receive its own size. Keep weak-cache keys weak and values scalar.

2. Add a fresh `IdentityHashMap` from function definition objects to scalar widths
   to each thawed Machine. This avoids taking the global weak-cache lock on every
   call. It is execution-local optimization state, excluded from snapshots and
   world context. Independent thawed forks get independent maps. Use an associated
   Machine extension key rather than changing the record definition. Already
   running Machines without this map can safely use the global weak cache until
   their next thaw.

3. Choose a local width only when entering an actual function. Resolve the
   function and validate its exact arity before querying its size, preserving
   existing unresolved-function and arity failures. Underapplication, erased
   application, Builtins, and their ownership rules keep their existing paths.
   Size by maximum register ID plus one, not parameter or binding count. Include
   parameter IDs, operand references, destinations, nested alternatives, join
   parameters, host destinations, and suspend destinations.

4. Honor explicit non-nil `:register-layouts`. Preserve its existing global-width
   fallback for missing entries; nil selects cached callee sizing. Keep lazy
   execution's clearing of potentially stale explicit layouts. The current
   function object supplies the width even when a compiled caller is reused
   after an implementation edit. No compiler-key change or register renumbering
   is needed for this storage policy.

5. The initial adoption retained program-wide Machine `:slots` and conservative
   thaw/frame/join reconstruction. The later restoration adoption below keeps
   `:slots` as a global fallback but sizes restored arrays from sparse live
   bindings and actual continuation requirements. Captured joins and synthetic
   continuations need their own widths, not a guessed callee owner. Frozen state,
   fuel and ownership remain identical under both physical-storage policies.

6. Non-tail calls still allocate a separate callee array: the saved caller frame
   owns its current array. Tail calls must replace oversized arrays to obtain an
   actual reduction. Exact-width reuse is the simplest policy to test, but can
   increase allocation when tail calls alternate between similar widths. A
   shrink threshold is a separate policy choice, not assumed beneficial here.
   Clear a reused array once; do not fill a newly initialized array a second
   time. Operand values must already be resolved before clearing caller storage.
   Register clearing must not introduce retain/release operations.

7. Preserve join captures and caller frames. Captured joins retain their own
   arrays; saved continuations must restore their original locals and join maps.
   The existing overapplication continuation reads and writes only register 0,
   so its fresh array can separately use width one. Surplus arguments remain
   owned by its existing immediate operands. Do not replace that resumable guest
   continuation with hidden host state or change saturation semantics.

Validation extends existing
[slot-count](../test/prototype/slot_count_test.clj),
[call compilation](../test/prototype/call_compile_test.clj),
[closure application](../test/prototype/closure_application_test.clj), and
[lazy runtime](../test/prototype/lazy_runtime_test.clj) coverage:

- Assert physical array widths with an unrelated register-4010 function inflating
  the global width. Verify a tiny callee uses its local width, a wide-to-tiny tail
  transfer shrinks, and returning to a saved wide caller restores its state.
  Test sparse parameters, high result/host/suspend destinations, and sparse join
  parameters and captured locals.
- Compare complete frozen state against the reference backend at every pause
  budget for small fixtures across mutable, demand JVM, and eager execution,
  including explicit compact layouts. Include region-boundary budgets, cold and
  warm code reuse, suspend/resume, host boundaries, globals, and backend switches.
- Fork paused snapshots independently. Check nested joins, closure captures,
  underapplication, repeated overapplication, returned Builtins, and invalid
  applications. Results, steps, resource release events, reference counts,
  continuations, and failure behavior must agree.
- Verify one measurement per immutable function identity, alias reuse, a fresh
  equal definition, and a changed definition under the same name. In particular,
  a reused compiled caller must enter an edited callee whose new body requires
  higher registers. Test mutable-code rejection, absence of execution caches in
  snapshots, independent fork caches, and existing weak-retention guarantees.
- Use deterministic operation counts and array lengths for optimization tests,
  rather than timing assertions. If `mutable/function-slots` adopts the shared
  cache, update its existing scan-count test to require cache reuse while keeping
  the protection against evicting the program cache.

The new [register-layout tests](../test/prototype/register_layout_test.clj) and
seven existing namespaces passed **67 tests / 12,147 assertions**, with zero
failures or errors, in one guarded 256 MiB JVM. Tests compare complete frozen
state at every fuel budget for small fixtures across reference, mutable, demand
JVM, eager, and compact eager execution. They check actual array widths, saved
caller restoration, sparse joins, host and suspension boundaries, forks,
overapplication ownership, exact-width allocation counts, weak identity caching,
mutable-code rejection, and compiled caller reuse after a callee changes.
The existing closure and region suites retain their broader saturation and
pause-boundary coverage. The result does not claim exhaustive equivalence for
arbitrary programs. See the [validation record](../measurements/register-layouts.json).

For the original function-entry adoption, add/refresh `slot-count/function-slots`,
`mutable/function-slots`, private `mutable/callee-slots`, `mutable/thaw`, and
`mutable/call-values!`. No new namespace alias, import, global cache definition,
or Machine record definition is needed. Every new thaw creates an associated
`:function-slot-cache` IdentityHashMap; it is excluded from snapshots. A Machine
already running without that extension safely falls back to the weak function
cache. Existing compiled helper code may retain its old storage policy until
recompiled, with the same guest semantics.

The actual live adoption canary passed in
`target/frontend-adopt-register-layouts.log`: the Machine class and unbound
sentinel were preserved, a program-wide width of 4,011 entered a tiny callee
using width one, and the complete frozen snapshot exactly matched the reference
result 42. The execution cache was absent from the snapshot. This establishes
that the function-only adoption preserved the checked runtime identities and
canary semantics.

The ordinary macro probe subsequently completed through a reviewed resume with
result 42, no diagnostics, and no pending initializers; its
[measurement](../measurements/hosted-ordinary-macro.json) records the resumed
interval separately from full compilation. There is no paired macro benchmark
or post-adoption allocation profile. The earlier 578/1,654 CPU samples justify
the investigated change but establish no measured speedup or allocation
reduction after adoption.


## Restoring live continuations and warm heap storage

A later [hybrid-finalizer diagnostic recording](../measurements/hosted-hybrid-finalizer-allocation-profile.json)
identified heap-validation traversal and `mutable/bindings` restoration work in
the active import path. It also records a separate extreme first allocation
sample. The sampled CPU frames and allocation weights diagnose candidate costs;
they are not exact allocation totals or a paired before/after benchmark.

The [register-restoration adoption](../measurements/hosted-register-restoration-adoption.json)
used the actual paused pre-handler state at guest step 782,389,421. Total restored
register capacity decreased from 120,330 slots to 2621, despite a program-wide
width of 4011. This extends local sizing to restored locals, saved frames and
captured joins using their actual sparse bindings and continuation requirements.
The complete frozen state, Machine class, unbound sentinel, heap and function
identities remained unchanged. The pause executed no handler and did not replay
guest finalization. Earlier rules retaining conservative global widths on all
restoration paths describe the prior policy, not the current implementation.

The separate [heap-storage hint adoption](../measurements/hosted-heap-storage-hint-adoption.json)
validated 1,386,420 existing local nodes once on the cold path, then performed
ZERO node validations on a warm restore. The actual host retain/allocate/replace/
release sequence preserved the derived storage proof. The same original frozen
state, Ref/Tag/Builtin/Machine classes and unbound sentinel were preserved, and
the checkpoint did not advance. The guest resumed from that same checkpoint on
2026-10-17 at 15:59:47 UTC; it was not restarted or finalized again.

`prototype.heap-hint` holds a bounded weak identity cache. Its proof concerns
standard persistent heap/node maps, vector field storage, and key-shape evidence
for the existing COW implementation. Freeze and validated reference-host updates
can propagate that proof to derived heap roots. A missed/evicted hint or an
unknown/external heap uses the cold validation/normalization path. External
mutable field arrays must still be copied and normalized. A hint is NOT a deep
payload immutability certificate, a native object/source witness, or kernel/code
checking authority; it must never substitute for any such admission check.

Consequently warm HEAP overlay creation can skip the full heap validation scan.
That is not an O(1) entire fork: globals still need restoration, frames/locals/
joins need arrays and bindings, and continuation sizing and dirty freeze work
remain. No speed ratio or steady-state import/compile throughput is inferred
from these correctness/operation-count observations.

The [combined validation](../measurements/heap-storage-regression.json) passed
**688 tests / 58,628 assertions**, zero failures/errors, in one guarded 256 MiB JVM.
It pins source SHA256 values for that exact generation and covers restoration,
warm hints and reference-host propagation. At that validation/adoption point,
the hybrid guest finalizer was still running and its strict final-kernel/B gates
had not passed. The [later B observation](../measurements/hosted-ordinary-library-b.json)
records that separate semantic success; these storage tests/adoptions themselves
do not establish it.

### Later 20-second diagnostic window

The [post-adoption recording](../measurements/hosted-hybrid-optimized-allocation-profile.json)
samples a later phase of the still-running genuine hybrid finalizer. Compared
with the [earlier diagnostic](../measurements/hosted-hybrid-finalizer-allocation-profile.json),
the named top-frame samples are:

| Diagnostic count | Earlier window | Later window |
| --- | ---: | ---: |
| All execution top-frame samples | 1916 | 1838 |
| `mutable/thaw-heap` named frames, including its reducer | 758 | 0 |
| `runtime-prim/evaluate` | 7 | 288 |
| `PersistentHashMap/hash` | 116 | 227 |
| `PersistentVector/arrayFor` | 109 | 126 |

The earlier 758 consists of 756 reducer samples, one older reducer frame and one
`thaw-heap` frame. Zero later samples means those named frames were not observed
at the top of sampled stacks; it does not establish that every possible cold
validation path disappeared. Primitive dispatch and persistent-map operations
now occupy the leading sampled frames.

Allocation-stack attribution also changed. The sampled weight at
`mutable/bindings` is 1,130,048,776 bytes in the earlier window and 10,482,792 bytes
in the later window. Its reducer-frame weights are separately 2,096,576 and
2,096,568 bytes. These are sampled attributed weights, not exact allocation
totals. Each record reports its extreme first allocation sample separately and
excludes it from these aggregates; no cause for those outliers is asserted.

The windows cover different phases and nREPL execution threads. They are bounded
diagnostics, not paired input runs, measured allocation rates, speed ratios or
steady-state throughput comparisons. They support leaving restoration work alone
while completing the current semantic gate. No further runtime optimization is
implied, and this recording does not establish finalizer completion, strict final
kernel association or B's successful import/compile/call.
