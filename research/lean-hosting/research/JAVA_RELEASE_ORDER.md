# Native-order release before guest finalizers

The experimental interpreter's finalizer-free destructor now follows pinned
Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` ordinary RC ordering.
It scans constructor fields, closure captures and live array elements in ascending
order, consuming each child-edge credit immediately. Only children reaching
logical zero enter the deletion worklist; those shells are then visited LIFO.
It completes the parent's batch before visiting any zero-owner child.

The prior loop queued all Node edges in reverse order and decremented while
popping them. It could finish the first child's subtree before consuming later
sibling credits. That distinction had no finalizer callbacks in the admitted
profile, but it must be corrected before implementing release-triggered Promise
propagation. Reversing the field loop alone would not fix the deferred decrement.

Queued zero shells are marked dead immediately, so an INC cannot resurrect them.
Their remaining fields stay available to the private destructor until scanned.
A live persistent RC0 node is distinct: releasing its edge does not queue, mark
or traverse it. Duplicate field occurrences consume separate credits and enqueue
a shared child only at its final edge. Spare array capacity never owns edges.
The traversal stays iterative; a 5,000-node chain needs no Java recursion.

The existing work array now has a private cursor, copied with that array in
branch state. Private batch/pop probes let the bounded tests inspect actual
production boundaries without registering executable destructor hooks. The
suite checks sibling order, shared grandchildren, duplicate edges, persistence,
array spare capacity, closure captures, queue growth and deep public DEC.
Snapshots and test references acquire no guest owner credits.

This ordering-only tranche remains synchronous and finalizer-free. A separate
[root release transaction foundation](JAVA_RELEASE_TRANSACTIONS.md) now provides
budgeted explicit root disposal. Neither tranche adds Promise, pending Task,
scheduler, logical MT metadata or general failed-execution cleanup. Default
synchronous DEC's existing work-array cleanup on terminal failure is not a
resumable ownership ledger. Native Task/Promise-specific nested release
boundaries, helper publication order, stacked Host cleanup continuations and
explicit active-mode disposal must be implemented before guest finalizers can
run. Public dec/close and the ready-only runtime profile are unchanged.

Pinned source: [child decrement/worklist](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp#L323),
[ordinary field scanning](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp#L379),
and [normal RC drain](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp#L475).
This source ordering is the non-LEAN_LAZY_RC profile, not a claim about all native
lazy/sticky/parallel RC configurations.

Integration evidence: the complete Java 11 isolated-jar gate exits 0 at
384 MiB, with 752 test executions / 21,782 assertions across 81 suites. The six
new tests pass with 55 assertions per driver; existing guest-export, code/host,
selected-owner, fork, Ref, array, scalar and ready Task.map suites remain included.
Independent source and batch/queue review found no blocker in this bounded scope.
The [active-runtime contract](JAVA_LOGICAL_TASK_RUNTIME.md) separately specifies
how quiet releases can avoid continuation allocation while stopping before any
actual guest callback dispatch.
