# Explicit JVM task runtime implementation contract

This is the next implementation contract, not a shipped capability. Authority is
Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and its original admitted
IR. The current [ready Task.map implementation](JAVA_TASK_MAP.md) remains the
default no-task-manager profile. The real command frontend currently stops at
`IO.Promise.new`; [the probe receipt](../measurements/java-ir-string-pos-2026-10-30.edn)
records that boundary. Header parsing succeeds independently of these tasks.

## Profiles and compatibility

Add an explicitly selected logical active profile to the existing explicit
interpreter. Native Promise.new panics without a task manager, so enabling
promises must not silently change the existing inactive profile. Initialization
phase and task activation are independent properties. Fork inherits both;
installing globals or code never activates a scheduler. The recursive driver
keeps its existing ready-only behavior rather than acquiring a second scheduler.

Active execution is single-threaded and cooperatively driven by the host.
Preserve deterministic synchronous ordering, results, cancellation flags and
ownership. Native parallel timing, dedicated workers and arbitrary native FFI
are outside this profile. Initially support ordinary native priorities 0..8,
higher first and FIFO among equal priorities, with bounded instruction quanta.
Reject other priorities before claiming inputs. No unpumped background progress
is promised. Root completion and scheduler quiescence are separate observations.

The first command gate remains original `compileImportedFileState` on a genuine
fresh guest Environment, empty executable roots and this original source:

```lean
prelude
axiom HostedSort : Sort 1
```

The sync frontend still creates pending promise maps and BaseIO.asTask work.
Ready-only shortcuts cannot complete it. Passing this gate will not establish
imported Init compatibility, theorem publication or frontend self-hosting.

## Ownership graph

Keep ordinary Node.fields owning. Runtime-created Task values own their current
value, callback and source in explicit kind-specific slots. Promise owns its
result Task. Pending slots may be internally absent, but never become guest
null values. Metadata contains primitive kind/state/priority/cancellation flags;
it must not hide guest references, host Futures or callbacks.

Use a separate branch-local TaskRecord graph for dependency registrations,
queues, waiters and current-task handles. These edges are nonowning in guest RC,
even when strong Java references preserve physical shells. A dependent owns its
source; the source's reverse registration does not own the dependent. Pure tasks
gain no scheduler keepalive credit. BaseIO tasks gain exactly one explicit credit
until final callback completion, including bind forwarding. This ledger is part
of fork and disposal, not an incidental Java collection root.

Unlink a waiting/queued pure task on its last DEC, release its captures and never
run it later. A running deactivated pure task finishes its already-owned callback
and discards the eventual result. Remove retired records and clear references.
Registrations need stable membership/backpointer state: an earlier synchronous
callback can delete a later entry after the source's list has been detached.

Initially admit pending Tasks and Promises only by runtime construction. Prepared
graph import must not acquire a new pending-value grammar accidentally. They are
branch-owned mutable values, with no sourceRC0 persistence. Foreign branches
must reject before claims. Guest-created RC cycles are not collected by this
runtime; scheduler links must not introduce additional owning cycles.

## Release transactions precede finalizers

Promise drop can run arbitrary synchronous guest callbacks. All releases must
therefore preserve their exact position relative to surrounding guest effects.
Audit IR DEC, constructor/closure release, Ref and Array helpers, owned Task.get,
callback capture disposal, host facade cleanup and external root release.

First correct finalizer-free destruction order: normal pinned native RC scans
fields in ascending order, decrements each edge immediately, then destroys
zero-owner children from a LIFO worklist. It does not recursively finish child
zero before decrementing the next sibling. Persistent children remain untouched.
Do not claim producer lazy-RC timing without verifying its configuration.
The target here is original-IR interpretation and runtime-primitive behavior.
C emission can use a known-field release optimization with sequential ascending
field releases, while IR lowering drops that annotation. Thus do not promise
identical destructor traces for every separately C-compiled source program.

Then add a private ReleaseFrame whose worklist and nested release boundaries
survive budget pauses, CodeRequest, HostRequest and fork. Do not call the Java
recursive evaluator from a finalizer. A primitive continuation must preserve
typed operands, output and its next disposition before yielding into release.
Release-before-store and store-before-release operations must retain their
native branch individually. Positive single-thread ST.Ref.set releases old before
publishing new, while native MT/persistent refs exchange before releasing old.
Task creation can transitively mark callback captures MT, including refs: it is
incorrect to apply the ST ordering universally just because Java schedules on
one thread. Track logical MT marking separately from positive guest-owner counts,
including its uniqueness/isShared consequences, and copy that primitive state
on fork. It is monotone: exclusive means `rc == 1 && !logicalMT`, and IR isShared
is the negation of exclusivity, not the native C `lean_is_shared` predicate.
Mark callback captures on actual active task allocation and mark values before
first task resolution; a losing duplicate resolve consumes its value without
marking it. Task.pure and inline sync-ready paths do not independently
mark. Mark new payloads before MT/persistent Ref.set/swap. Array.uset releases
old before storing; Array.pop lowers its live size
before releasing its item. Reentrant access to a destroyed shell must reject
safely; matching native values does not require reproducing unsafe memory access.

Public active-mode root release needs `startRelease` plus the existing explicit
advance/request/resume protocol, or an equivalently explicit transaction API.
The synchronous public dec entry remains usable only for the old finalizer-free
profile and must reject incompatible active calls before mutation. Internal
release joins the current continuation. Host borrowed-facade release cursors
must resume exactly once, including nested host callbacks. Close remains
non-executing and rejects active work; normal draining and finalizer execution
are explicit operations, including disposal of private positive cache credits
which external-value release alone cannot discharge. Terminal failed frames retain diagnostic owners; do
not execute new finalizers as implicit error cleanup or replay failed effects.

## Operations and ordering

| Operation | Required behavior |
| --- | --- |
| Promise.new | Allocate one promised Task owned by one Promise; native inactive profile rejects. |
| Promise.result? | Retain and return the same result Task identity, not a new task or a forced result. |
| Promise.resolve | First value becomes Some(value); later values are consumed/discarded with their release effects. |
| Promise drop | Resolve None if pending, finish synchronous propagation, then release its Task owner. |
| Task.get / IO.wait | Retain ready value before consuming Task. Pending get parks an owned continuation; actual sync-task pending get rejects. |
| Sync map on ready source | Apply inline in the caller's task scope and wrap the value in a ready Task. |
| Sync bind on ready source | Apply inline and return the exact callback Task, including a pending one. |
| Pending map/bind | Move callback/source into a dependent; return it without pretending readiness. |
| Async ready map/bind | Queue a distinct task rather than taking the sync-ready shortcut. |
| Source finish | Detach registrations in LIFO order; each sync callback and nested propagation finishes before proceeding to the next. |
| Bind forwarding | Wait on a returned pending Task while preserving outer identity and BaseIO keepalive; forward its value without a second callback. |
| Cancel | Set a flag, without resolving or skipping the task. Propagate source cancellation at completion. |
| checkCanceled | Observe current task scope; inline ready callbacks inherit their caller's scope. |

Callback application uses the ordinary explicit AP machinery, including boxed
wrappers, PAP captures, oversaturation and original body demand. A CodeRequest
can already own its transferred activation arguments: validate the exact
materialized reply before resuming, preserve those owners, and never repeat
get/AP or their claims. Host replies preserve existing one-shot and provenance
rules. A callback's task scope survives code/host pauses and is
restored at the native boundary before result propagation. Release BaseIO's last
keepalive while still in that callback scope.

Promise.result! and CancelToken remain original guest code. Option.getOrBlock!
on None is an explicit unsupported panic/blocking path, never a synthesized value.
CancelToken.set resolves its Promise before writing its Bool flag: an onSet
callback can observe false, and set returns after sync callbacks with true.

## Contexts, host boundaries and fork

Factor per-execution registers, numeric words, joins, stack/frame pointers,
active Function/PreparedBody, PC, continuation actions, claims and task scope
into saved ExecutionContexts. Code/global state and the guest heap remain shared
within one branch. Preserve exact raw F64/U64 packets and prepared-body identity;
do not own every stale register merely because a context is saved.

Queue callbacks start with an explicit task-completion action. Parked root/task
contexts allow queued producers to run. Expose WAITING if no context can run;
never busy-spin or return fake success. An actual sync task waiting on a pending
task follows the native rejection rule. Bound contexts, queues, registrations,
release depth and instruction work as well as ordinary stack depth.

Initially a CodeRequest or HostRequest pauses the whole engine, with only one
externally outstanding request. Do not reorder unrelated effects while an
arbitrary host operation is outstanding. Code publication is branch-wide, while
saved contexts retain their exact body generations. Later external resolution
of a parked root requires an explicit control transaction, not reentrant start.

Fork at an explicit safepoint with the existing single guest-value memo, plus
an identity memo for TaskRecords, registrations and saved contexts. Remap every
nonowning link to its child shell; copy primitive mutable state and all owning
ledger credits once. Preserve closures, external roots, pointer identities and
code generations under their existing contracts. A child must never retain a
parent scheduler link. Fork at pending/new, detached propagation, queued/parked,
bind-forwarding, release, code and host boundaries, then resolve independently.

## Quiet release and uncommon dispatch

The active release protocol must preserve a cheap ordinary path. Internal
`beginRelease(value, count)` returns `QUIET_COMPLETE` or `NEEDS_DISPATCH` as
private control outcomes, never as guest data or a thrown suspension sentinel.
A valid decrement leaving positive RC completes without allocating a frame.
Ordinary native-order destruction can also finish inline in reusable work
buffers. Quiet completion means all required effects finished, not merely that
the graph had no special kinds.

Stop before applying any guest callback, including a prepared callback. Preserve
the release cursor, nested boundaries, propagation position and committed owner
dispositions. The caller then saves its typed operands/output and exact suffix,
attaches the pending release and returns control to the central dispatcher.
Only that dispatcher may enter the callback. Do not advance the PC, publish a
result, apply surplus arguments or release later operands in the meantime.

Reusable ReleaseScratch and NativeOpScratch hold ownership-bearing intermediates
before mutations which might suspend or fail. Promote that state into a private
continuation only at the uncommon boundary, preferably using reusable frame
storage. Scratch participates in fork whenever nonempty. If promotion fails,
preserve the interrupted operation and unfinished destruction for terminal
diagnostics; this does not promise recovery from arbitrary JVM OOM. Grow work
buffers before detaching the next edge where practical. Do not clear unfinished
active-mode work in an unconditional finally block.

For Array.uset the saved suffix stores the incoming value and returns the saved
array. For MT Ref.set it returns Unit, since exchange already happened. For host
cleanup it finishes the current release, advances that borrowed-argument cursor,
then considers the next argument. Keep separate nested HostCompletion records
when an outer claimed reply's cleanup creates another HostRequest. Every root,
FAP, AP and helper path must propagate the outcome. No graph-wide may-finalize
prewalk or transitive finalizer cache is required; public active-mode release
still uses the explicit transaction API.

## Implementation sequence and acceptance

1. Native-order finalizer-free release, with focused shared-child/order tests;
   retain current corpus behavior and bounded complete gate.
2. Resumable release protocol and primitive/host continuations, plus explicit
   active-profile selection and same-memo fork coverage. No Promise callbacks
   until these boundaries are complete.
3. Promise lifecycle, pending sync map/bind, BaseIO keepalive and original guest
   cancellation. Verify aliases, first-write/drop, deleted registrations, nested
   LIFO callbacks, callback pauses and both branches after fork.
4. Runnable contexts, spawn/asTask, async dependencies, pending get and bounded
   pumping. Separate root result from runtime status. Verify no-runnable WAITING,
   equal-priority rotation and dropped pure versus retained BaseIO work.
5. Retry authenticated prelude axiom, then a checked theorem, emitted callable
   identity and imported Nat example. Follow actual missing operations instead
   of broad replay. Kernel admission/publication and interop are separate gates.

The [native oracle](../test/fixtures/java-task-active-runtime/README.md) already
observes first-write Promise resolution, dropped-promise None, third/second/first
sync callback ordering and CancelToken callbacks observing false inside set.
It is reference evidence, not passing JVM task-runtime tests. Future JVM tests
must use these observed semantics, exact original ABI rows and meaningful owned
values, including losing resolve payloads and callback-triggered releases.

Source anchors at the pinned commit: `src/runtime/object.cpp` task/Promise
implementation and RC worklist; `src/runtime/io.cpp` BaseIO tasks and ST.Ref;
`src/include/lean/lean.h` array/Task ABI;
`src/Init/System/{Promise,CancelToken,IO}.lean`;
`src/Lean/Language/Lean.lean` command task graph.
