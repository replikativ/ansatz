# Transactional prepared graph and global import

Implemented research profiles, 2026-10-30. This adds supported graph construction
to the Java engine. The default profile accepts **only genuinely persistent
RC-zero source nodes**. Explicit selected-owner import also accepts positive
source metadata. Neither profile is a general checkpoint importer or frontend
acceptance claim.

## Source and descriptor contract

The trusted adapter authenticates the prepared-state manifest/rows and their
compatibility with the accepted code SourceBinding. The engine receives a
lightweight accepted-state identity token, not a full source catalogue. Supplying
a token, source ID or claimed RC count does not authenticate input bytes.

The closed public descriptor API is:

```java
new GraphRef(long sourceId);
ImportNode.ctor(long id, int sourceRC, int tag, Object[] fields, byte[] scalars);
ImportNode.array(long id, int sourceRC, Object[] elements);
ImportNode.ref(long id, int sourceRC, Object value);
ImportNode.closure(long id, int sourceRC, Header target, Object[] captures);
new PreparedGraph(SourceBinding binding, Object acceptedStateToken,
    ImportNode[] nodes, Header[] globals, Object[] globalValues, Object[] ownedRoots);
Object[] engine.installGraph(PreparedGraph graph);
```

In the default constructor every sourceRC must be zero. Graph values are GraphRef edges or supported
immutable nonnegative Long/BigInteger/String carriers; existing runtime Nodes,
arbitrary host objects and external/native handles reject. Descriptor arrays and
scalar bytes are copied. Every source ID must be unique and every edge must
resolve inside the new graph. All descriptors must be reachable from declared
global values or returned roots; orphan records reject.

Constructors have tags 0–243, fewer than 256 object fields and fewer than 1,024
packed scalar bytes, matching the pinned Lean header bounds. A scalar-free,
field-free constructor is supplied as an immediate Long tag, not a heap record.
Arrays contain live object elements only. A ref has exactly one payload, no
scalar storage and a distinct runtime kind flag; its numeric tag alone never
grants ref identity. Closures require an exact current registered Header from
the same SourceBinding, supported boxed object parameters/result and strict
underapplication. Borrowed array primitives still require proper boxed wrappers.
Closure admission never forces its body.

This first profile caps nodes, globals and returned roots at 100,000 each; total
value occurrences at one million; aggregate scalar bytes at 16 MiB; and estimated
immutable-carrier bytes at 16 MiB. Overflow-safe bounds precede graph allocation.
These are research admission limits, not a complete Lean data-format claim.

## Publication, ownership and forking

Import requires an open IDLE engine without active/failed execution, a pending
result or a host/code request. One successful transaction is permitted per engine,
including empty transactions. Forks inherit that marker. Incrementally importing
overlapping source IDs would duplicate source identity without a persistent
resolver; this API does not silently provide that behavior.

Global destinations must be exact registered nullary initialized Headers with
object results in the same SourceBinding. Their cache slots must be unoccupied.
Staging executes neither global sentinel bodies nor initializers and does not
mark modules or initialization phases complete.

Validate the entire recipe, allocate shells, then wire all fields/captures through
one temporary ID map. This preserves repeated aliases, self references and cycles.
Allocate return roots, replacement constant/readiness arrays and immutable global
provenance before publication. A rejection leaves the engine and one-shot marker
unchanged. Abandoned resource-free unpublished graphs are left to JVM GC, without
logical decrements of partially constructed state.

All nodes admitted by the default constructor retain RC-zero persistence. Returned roots are independently
owned outputs by contract, with no new positive credits for duplicate aliases in
this profile. The engine retains lightweight per-global source/state provenance,
not the PreparedGraph, node recipes or a permanent source-ID registry. Temporary
construction references are not guest owners and disappear without inc/dec.

The existing graph fork copies mutable ref cells, their values, globals, closures,
constants and execution control through one memo. Refs remain mutable despite
RC-zero persistence. Ordinary constructor projection, unboxing, cases and unique
mutation paths reject refs. The graph-import milestone used explicit Java host
ref access; the subsequent [native ref runtime](JAVA_REF_RUNTIME.md) supplies
get/set/swap/take/ptrEq/mkRef without host requests.

## Evidence and subsequent gates

Seven focused tests / 61 assertions cover cyclic aliases, duplicate roots, global
readiness and provenance, forked ref identity/mutation, authentic unforced closure
execution, array aliases and packed scalars, malformed/foreign/orphan recipes,
one-shot and idle-only publication, bounded rejection and facade shape checks.
The combined isolated jar gate passes 366 test executions / 13,554 assertions in
a 384 MiB JVM. Independent implementation and facade review found no remaining
blockers after aggregate bounds and ref kind guards were added.

The [implementation record](../measurements/java-ir-prepared-graphs-2026-10-29.edn)
pins the tested source/jar and retains both complete paired computational controls.
Allocation stayed at 1,515,859.52 bytes per RBMap run. Timing varied substantially
between controls and earlier observations in the retained shared-machine JVM;
these results establish no speedup or stable CPU-overhead estimate.

The genuine ppExt experiment now installs its nine persistent nodes and the two
actual ready globals `Lean.ppExt` and `Lean.ppFnsRef` through this API. It imports
ten authentic headers, forks at the first code demand, and each branch loads the
two original initializer bodies. The five returned callback bodies and both
global sentinel bodies remain unprepared. There is no reflective Node construction.
This first graph-import probe used the exact `lean_st_ref_get` host ABI. The native
ref-runtime probe replaces that handler with the actual engine primitive; neither
gate is full parser support.

## Explicit selected-owner profile

`PreparedGraph.selectedOwners(binding, token, nodes, globals, values, roots)`
uses the same transaction and shape checks, with an explicit ownership policy.
ImportNode factories describe nonnegative source counts; only graph admission
selects the policy. The default constructor continues rejecting positive counts.

Source RC0 remains persistent. For each source-positive object, the destination
count is recomputed from every owning occurrence in constructor fields, live
array elements, closure captures, ref payloads, global caches and owned output
roots. Edges from persistent parents count too. Duplicate occurrences count
separately. The source count's positive magnitude is ignored: absent outside
owners must not be carried into a closed selection. Counts use checked addition;
zero-count positive objects reject. These are trusted source facts, not a proof
that arbitrary host-supplied RC metadata is truthful.

Closed cycles are permitted and retain native RC behavior. Logical RC does not
collect cycles; programs must break their logical owning cycles where required.
JVM GC still collects physically unreachable Java graphs. Forking copies the
complete selected graph and its counts without creating extra guest credits.

`new GraphInt(BigInteger)` transports an exact signed Lean Int only in this
profile. Signed 64-bit values normalize to Long; larger magnitudes remain
BigInteger. Descriptors disappear during wiring, including globals and outputs.
This does not reinterpret UInt64 bits or implement Int arithmetic. Raw negative
Long/BigInteger leaves still reject; the default graph rejects GraphInt everywhere.

Seven focused tests, invoked with both driver configurations, cover duplicate edges/roots, persistent
parents, cache cleanup, a positive self-cycle broken with the original boxed
ST.Ref.set wrapper, closure capture ownership across explicit-driver code suspension/fork,
signed boundaries, and failed-import retry. The original seven RC0 tests remain
unchanged. A retained 384 MiB REPL also imports and forks the actual selected
frontend companion: 47,240 nodes, 2,417 headers, five globals, 1,302 positive
objects (all recomputed RC1), and 113,703 scalar bytes. Both graph censuses agree.
The first observed engine installation took 64.26 ms and fork 39.69 ms, excluding
capsule parsing/header/descriptor preparation. These are single-run observations,
not steady-state performance estimates. The capsule is derived experimental
input, not yet a public authenticated bundle loader. Frontend execution, complete
initialized/module state and imported module/kernel carriers remain separate gates.

The REPL facade's `lean-name-data` converts nested immutable Java Name lists to
Clojure vectors before persistent-map lookup. Java collection hash codes and
Clojure collection hashes differ; preserving exact tags/leaves avoids silently
missing a valid header during cross-language lookup.

## Opt-in persistent-Ref payload sharing reconstruction

`PreparedGraph.selectedOwnersWithPersistentRefPayloadSharing(binding, token,
nodes, globals, values, roots)` uses the existing selected-owner ledger and an
additional explicit target-sharing policy. The research facade exposes it as
`selected-owner-ref-payload-mt-graph`. Existing RC0 and `selectedOwners` recipes
remain unmarked; neither silently opts into this policy.

This profile requires every imported Ref to be persistent. Global-cache and
owned-output roots cannot directly reference a positive node. Every owning edge
from a persistent non-Ref must target a persistent node or immediate value;
only persistent Ref payload slots may cross from persistent to positive storage.
Starting at those slots, a bounded identity walk follows all owning fields and
captures through positive nodes, stops at persistent nodes, and requires every
positive descriptor to be covered. Duplicate edges and cycles preserve the
existing selected-owner counts. Source-positive numeric counts remain descriptive
and are never copied. No extra root, traversal or marking credits are added.

These boundaries are checked before shell creation. After all new shells are
privately wired, the existing logical-MT walk marks their persistent Ref payloads.
The resulting marker mask must exactly match the descriptor-derived region before
any cache, source provenance, allocation counter or one-install marker is
published. Marking preserves closure Generation, object-array live size and
ByteArray state; pointer observation and fork continue using their existing
wrappers. No source-ID table, derived mask or graph recipe is kept by the engine.
A failed staging operation leaves the engine available for a valid import retry.

The source basis is pinned Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:
[mark_mt](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp#L663)
walks owning children while stopping at persistent/already-MT objects;
[Ref.set/swap](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/io.cpp#L1495)
marks an incoming payload before publishing it through a persistent/MT Ref;
[exclusivity](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h#L704)
requires single-threaded RC1. Consequently an imported marked payload taken from
its Ref stays nonexclusive even after its count reaches one. Native array and
ByteArray mutation then copy to fresh ST storage; publishing that new storage
through the persistent Ref marks it again. Fork preserves MT while copying mutable
kind state and retaining immutable code Generation identity.

This creates an explicit target logical-MT global-registry template. Source/state
association still requires the same actual accepted tokens. An RC-only producer
capture does not supply historical native MT bits; the new profile does not prove
its initializer trace, allocation/alias parity or native execution history. It
adds no native carrier kind, Task/Promise import, thread scheduler or finalizer.
The five-kind grammar, 100k-node/1m-edge/16MiB budgets and one-shot transaction are
unchanged. Logical RC cycles are still not collected.

Seven focused tests passed 100 assertions in each of recursive and explicit
configurations in the existing retained 384 MiB REPL, using Java source SHA-256
`cb634d92c8da5d06eb8f8ac5c10adce31d2073f37ac701dce1d2e00c7f314641`
and immutable runtime jar SHA-256
`fd1391656211f135c3bda326a4cbdcfcd731fd5618fa2b342b8eb106ef9f8eca`.
Independent source review found no blocker. The tests cover old-profile
compatibility, atomic positive-boundary negatives even when also Ref-covered,
duplicate owner occurrences, source-token identity, take-to-RC1/COW/Ref.set,
closure AP and Array/ByteArray/Generation/pointer fork metadata, a positive cycle,
and a 4,096-node chain. Private field inspection is test-only. Bulk frontend
capture acceptance and the complete regression gate are separate observations;
this result does not claim that either has run with the new profile.
