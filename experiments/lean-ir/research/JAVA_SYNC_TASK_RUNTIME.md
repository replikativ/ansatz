# Logical synchronous task runtime implementation

Work in progress. This branch starts from the logical sharing and finalizer-free
root release APIs. It does not yet enable Promise construction, registrations,
callbacks, cancellation or an active frontend. The explicit TaskRuntime selector
currently exercises the control foundation only. Default constructors keep the
existing inactive and recursive behavior.

## Control foundation

RuntimeAction is private engine control and ownership state, never NodeMetadata.
Its receiver reserves one object scratch slot, captures the exact continuation
and keeps moved operands/output across a release. It does not invent a guest
Function or invoke the recursive interpreter. Generic AP will return full boxed
results into that slot; source calls keep their own real Function/layout.

Ordinary shared decrements and ordinary zero-shell destruction complete inline
using reusable scratch. They allocate no release continuation and execute no
callbacks. A budgeted external root uses an action; quiet ready Task retirement tail-drains
its sole value before the enclosing queue without allocating one action per Task.
Generic destruction scans every owning edge ascending before visiting queued
zero shells LIFO; Task retirement starts a nested boundary. Failed scans retain
current shell, cursor and queue. No finally block clears active unfinished work.
The pending implementation must stop this quiet scan before Promise/task
finalizers and promote its exact suffix before running any guest callback.

Native actions preserve ST Ref.set release-before-store, MT/persistent exchange
before release, Array.pop size reduction before release, Array.set release before
replacement, and replicate(0) payload release before returning the empty array.
Known moved operands and retiring owners remain in diagnostic action slots even
when their original container edge has been detached. Stale aliases in these
slots are not additional guest credits.

Claimed Host replies enter a cleanup action. The borrowed cursor stays on its
current credit until the release completes. Linked HostCompletion records retain
outer typed replies and ownership dispositions while nested requests run. Public
active dec rejects before mutation. startRelease uses the normal explicit drive
protocol and returns Unit through takeResult. Pending callbacks are still
unimplemented; consequently nested callback-request behavior is not yet claimed.

## Quiet release audit

Before callbacks can be enabled, the following local proofs are required for
remaining calls to releaseQuiet. This is a closed implementation audit, not a
public promise that arbitrary user values cannot contain finalizers.

| Call site | Local proof / disposition |
| --- | --- |
| Array COW | Every live copied edge is retained before the old array is released. |
| Array toList | Every output head owns a retained input element before input release. |
| Validated list toArray | All heads retained; destruction can only retire validated ordinary list cells. |
| Shared/MT closure AP | Every capture retained before old shell release. Exclusive ST transfer uses DEL. |
| Ready Task.get and ready map | Sole value retained before Task release; no arbitrary value loses its last credit. |
| Nat/String/ByteArray helpers | Validated immutable carriers, character-list cells or zero-owning-edge byte payloads. |
| Recursive evaluator | Inactive profile only; active construction requires explicit driver. |
| close | Active mode requires completed explicit disposal; it cannot discover and execute finalizers. |

Every genuinely arbitrary drop instead requires beginRelease and an exact saved
suffix: IR DEC, public disposal, Ref.set, Array.pop/set, replicate(0), duplicate
resolve, Promise drop, task capture disposal and Host borrowed-facade cleanup.
The last four task/Promise cases remain to be implemented and tested.

## Disposal and lifetime

startDispose moves engine cache/stdout credits into an explicit action ledger;
external owners remain the caller's separate responsibility. Retired cache IDs
are tombstoned and cannot replay initialization. First-time evaluation of new
closed constants during a future disposal callback is allowed. The sweep repeats
for owners published behind its cursor, so they are retired before completion.
SourceRC0 persistent globals and ordinary guest RC cycles are not collected.

Fork copies action/control/claim state and guest graphs through one identity
memo. It copies dead queued shells and remaining owning edges without changing
RC. This retains the existing pointer/closure/value provenance discipline;
it does not prove arbitrary unstamped host Node references belong to a branch.
Failure is terminal and preserves diagnostics; cleanup after arbitrary failure
and branch abandonment remain unimplemented.

Before this tranche is complete, pending task records, detached LIFO
registrations, current-task scopes and BaseIO keepalive ledgers must be forked by
that same memo, all entry paths must have preclaim validation, and callbacks must
pass Code/Host pause/fork/failure gates. No queued task contexts, asTask, async
scheduling or original command declaration success is claimed by this work.

After disposal, only diagnostics, the one Unit takeResult and nonexecuting close
remain supported on that session. startRelease, start/invoke, inc, makeClosure,
installGraph/installProgram, finishInitialization and fork reject before claims.
External guest owners must be released before private disposal. This is a host
precondition, not an inferred proof that every external alias was supplied.

Disabled-callback checkpoint integration (2026-10-30): the complete isolated
Java 11 jar gate exits 0 at 384 MiB, with 817 test executions / 22,628 assertions
across 85 suites. The added explicit foundation suite contributes eleven tests /
90 assertions. Independent control/fork/lifetime review found no remaining
blocker for this checkpoint after fixing legacy-root quiet release guards,
terminal disposal preflight, iterative private-record fork filling, quiet nested
ready-task retirement and complete repeated cache/stdout disposal sweeps.

This evidence covers the checkpoint with Promise native operations and pending
callback dispatch absent. It is not clearance for enabled callbacks: their
receiver, code/host suspension, nested cleanup, cancellation and failure behavior
require separate tests and review in the next change.
