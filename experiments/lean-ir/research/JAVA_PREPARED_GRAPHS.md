# Transactional prepared graph and global import

Implemented research profile, 2026-10-29. This adds supported graph construction
to the Java engine. It accepts **only genuinely persistent RC-zero source nodes**;
it is not a general checkpoint importer or frontend acceptance claim.

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

Every sourceRC must be zero. Graph values are GraphRef edges or supported
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

All admitted nodes retain RC-zero persistence. Returned roots are independently
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

The larger selected companion has positive-RC nodes, so it does not pass this
profile. Its follow-up needs an explicit selected-owner ledger: count each owning
field/capture/ref slot, global cache and returned owned root, preserve genuine
RC-zero persistence, and never copy source counts for outside owners absent from
the new graph. Prove cycles, exclusivity, aliases and failure behavior before
using that policy. Runtime ref primitives, complete initialized/module state and
imported module/kernel carriers remain separate campaign gates.

The REPL facade's `lean-name-data` converts nested immutable Java Name lists to
Clojure vectors before persistent-map lookup. Java collection hash codes and
Clojure collection hashes differ; preserving exact tags/leaves avoids silently
missing a valid header during cross-language lookup.
