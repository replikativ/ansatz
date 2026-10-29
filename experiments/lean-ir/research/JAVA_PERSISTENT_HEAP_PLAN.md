# Java execution regions and persistent heap plan

Status: source-grounded research/review plan, not a forkable Java implementation.
References to Klara below are paths within the sibling `klara` repository as
audited on 2026-10-28; its design is not treated as shipped Ansatz behavior.
The current direct engine remains the closed-execution performance control.

## Authority and first integration

Klara's `rfc/0005-affine-regions.md` confines editor authority to a region/fiber,
not a Java thread, and rejects multi-shot capture through a live exclusive
region. `src/klara/world.clj` pins immutable definition roots; later publication
does not rewrite retained children. `src/klara/authority.clj` separates tokens
from the authority they resolve. Its general memory design is broader than
the implemented runtime and is not a completed persistent-graph substrate.

For Ansatz keep three facts separate: guest RC, permission to mutate physical
Java storage, and external authority. RC1 alone grants no mutation right over
arrays shared with a retained snapshot. Aliased refs also need stable logical
identity; they cannot simply require RC1 for writes.

The first Java/provider adapter should be a closed pure region under existing
checked Contexts, after ordinary target/source/closure validation:

- Begin with Nat/String boundary codecs and no escaping Node/closure/ref/stream.
- Validate the transitive IR/extern closure. Deny callbacks, IO, mutable globals,
  tasks, resources and finalizers; reject unknown dynamic targets initially.
- Fall back only before entry. Never rerun the ordinary engine after Java has
  started, failed, or consumed arguments.
- Share immutable Programs; use a fresh private engine first. Any failed engine
  is discarded. This is whole-region abandonment under no-escape constraints,
  not general logical-RC cleanup.
- Preserve admitted declaration/version identity and source leases. Java
  preparation does not replace checking authority or guest publication.
- Keep Java dispatch budget distinct from World fuel. Do not claim identical
  intermediate checkpoints or a fourth interchangeable World backend.

Later engine pooling requires exclusive invocation leases, clean successful
state, detached results, and no mutable engine shared by Context forks. Kernel
or `evalConst` callback replacement is not part of this first application tier.

Use the existing resident call gate and facade rather than a new loader:
`resident_frontend.clj` validates FileHandle identity, ready units, boxed ABI and
protected dependency closure; `frontend.clj` installs admitted compiler output;
`project_loader.clj` owns graph/version semantics. Existing builtin operations
maps offer a later path for direct-node carrier adapters. Kernel/environment
and import-region identity bindings need separate migration.

## General heap model

The semantic lookup is `(branch root, logical identity) -> current version`.
Copying a node without redirecting all aliases, or only marking root RC shared,
does not provide isolation.

1. Assign identities with a lineage/allocation namespace; sibling counters must
   not collide. References in registers, fields, closures and handles name the
   same logical object even when its physical version changes.
2. Resolve inherited aliases through a branch store, including aliases reached
   from freshly allocated local containers. Store dead tombstones so removal
   cannot resurrect an inherited live object.
3. Use owner epochs for private fast paths. Publication revokes old mutation
   rights in both continuing parent and child; each advancing branch gets a
   fresh token.
4. Separate header and payload ownership. RC-only writes should shadow a header,
   not copy a large array. First payload mutation performs COW. Destruction and
   shell deletion must not clear arrays still visible to another branch.
5. Fork duplicates branch views, not guest edges: preserve each branch's initial
   guest RC counts. Guest allocation/retain remains distinct from physical COW.
6. Add derived resolution caches only after uncached correctness. Canonical
   versions must be stable within an epoch or cache installation must invalidate
   stale entries. Bound overlays/caches so long REPL histories do not retain
   retired branches or create unbounded lookup chains.

An eager alias-preserving graph clone is useful as an explicit O(reachable
graph + payload + control) oracle/fallback. Memoize across all roots and cycles;
separately cloning roots breaks cross-root aliases. Do not present it as cheap
persistent forking or let it become the architecture through incremental patches.

## Machine state and cleanup

Capture includes Program/basis, heap root/allocation namespace, active PC,
register and join ranges, continuations including surplus arguments, pending
result/phase/ownership, cache values AND readiness, runtime roots, output state,
counters/limits and supported host-boundary state. Recursive execution captures
only at entry/exit; the explicit driver supports instruction boundaries.

Constants own values and affect initialization/reuse; they are not a disposable
lookup cache. UTF-8 memo data is derived and may be discarded. AP staging and
release scratch must be empty at published points or explicitly represented.

Registers are not an owner ledger: copies do not retain and stale aliases remain.
AP can transfer captures before a later failure. General disposal needs prepared
ownership/liveness maps or a compact dynamic ledger for owning roots, cache
owners, moves, borrowed aliases, surplus arguments and runtime roots. Stage
transfers before subsequent fallible work and escrow the actual failure/result
packet before validation. Never retry destructive cleanup after it began.

Private no-escape regions may be abandoned to JVM GC. General cancellation
cannot decrement every nonnull register. GC does not restore external close
authority or prove guest RC reached zero; a rooted ID registry can itself retain
unreachable cycles and needs a pruning/compaction policy.

Virtual output should become an immutable journal/prefix plus private tail.
Forked private methods need stable provider identities resolved through branch
state, or explicit rebinding in the eager clone. Do not remove the existing
private-owner guard. Real output settlement has separate authority; restoring
guest state does not recreate a spent right or guarantee durable exactly-once IO.

## Sequence and discriminating gates

Finish bounded runtime evidence, then the pure provider adapter and the initial
Nat/String DSL/Lean declaration round trip. Specify the snapshot/ownership
packet; add eager graph capture as a control; implement branch versions/header
and payload COW; then owner-epoch fast paths, disposal and broader effects.
The narrower DSL gate need not wait for arbitrary refs or escaping closures.

Required cases include cross-root/captured aliases, a local container pointing
to an inherited node, fork at RC1, RC-only large-payload touches, unique/shared
closure application, pending constant initialization, nested forks after cache
population, sibling allocation identities, release tombstones, output isolation,
and injected failures around ownership transfer. Compare with eager capture and
the existing World implementation for overlapping profiles.

Measure closed execution separately from first capture, frozen-root fork, first
inherited read, header-only and payload writes, resume/disposal and retained
memory. Vary graph/payload/touched fraction/branch depth/control depth. A heap
fork may be O(1) while control capture remains O(live stack). Use a provisional
5–10% closed-execution overhead gate as an engineering target, not a prediction.
Typed JVM/JIT regions must preserve this same heap/effect contract; suspension
requires explicit frames or deoptimization/state maps.
