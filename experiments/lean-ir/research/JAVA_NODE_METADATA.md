# Compact kind-specific Node metadata

The array runtime's live-size field enlarged the shared Node layout, increasing
allocation in the unchanged tree workload by119,232 bytes/run. That cost applied
to ordinary constructors and closures, even though they need no array counter.
Move the counter into private kind-specific metadata and reuse the former closure
image reference slot; do not add another reference to every node.

The common Node keeps tag/RC, object/scalar storage, closure target and kind flags.
For the unmarked, unobserved values covered by this original layout receipt,
its one `NodeMetadata` slot has these alternatives:

| Kind | Metadata | Fork policy |
| --- | --- | --- |
| Ordinary constructor, ref, ready Task | null | no allocation |
| Object Array | private ArrayState(live size) | fresh copy per copied Node |
| Closure | immutable lightweight Generation | shared ancestry token |

`NodeMetadata.copyForFork()` requires an explicit policy for each metadata type.
Metadata owns no guest values; it cannot hide an owning Node edge outside the
existing alias-preserving graph memo. ArrayState is private to its one array;
fork's Node identity memo therefore makes exactly one independent state copy.
Generation retains the prior immutable jump-token ancestry and no Program/table
backreferences. Future metadata kinds must preserve the no-guest-owner contract.

Node.fields remains final array capacity, with a null spare suffix. ArraySize is
now available through `Node.arraySize()`; array operations/import/release and
fork semantics are unchanged. Closures retain their exact Function/generation
compatibility. The private field rename is reflected in research diagnostics;
this is not a new public source/bundle format or a data-admission relaxation.

The final artifact's paired retained384MiB control restores allocation exactly
from1,635,091.52 to1,515,859.52 bytes/run in both drivers, matching the earlier
native-ref baseline. This saves119,232 bytes/run, about7.3% against the enlarged
layout. Array objects now allocate one small ArrayState; the improvement is for
constructor/closure-heavy workloads and is not a claim of universal memory savings.
The recursive CPU medians were1.84/1.90ms and explicit2.26/2.19ms, prior/compact;
these mixed shared-machine observations establish no stable CPU improvement.

Existing array8/79 per driver and generation17/145 gates pass, along with the
complete isolated jar gate:474 executions /16,380 assertions across57 suites at
384MiB. The actual six-root companion imports and forks49,645 nodes,2,631 headers
and6 globals with unchanged census/owners/scalar bytes. Independent representation
and final fork-contract review is clear. A comment-only clarification compiles to
all27 byte-identical class files, preserving the tested artifact's bytecode.

This fixes a measured layout regression. UInt64/Float lanes, ByteArray descriptors,
Task.map, larger state fixed points and the complete frontend remain separate
campaign gates.

The [logical sharing foundation](JAVA_LOGICAL_SHARING.md) adds a lazy immutable
sharing wrapper under optional pointer metadata. Common Node layout is unchanged;
kind access and fork preserve the inner generation/array/byte-array state.
