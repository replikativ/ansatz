# Explicit logical synchronous task runtime

This experimental Java profile implements synchronous dependency propagation,
not native threads or the queued Lean task manager. Select it explicitly with
`TaskRuntime.logicalSynchronous()` and the five-argument Interpreter constructor;
the driver must be explicit. Default constructors retain the inactive ready-only
profile, including the existing recursive backend. Initialization phase,
BuildIdentity and task-runtime selection are independent. SourceBindings remain
trusted-adapter identities, not self-authenticating hashes.

The facade selects the profile with `:task-runtime` and
`logical-sync-task-runtime`. Use `startRelease`/`start-release!`, normal
advance/request/resume and takeResult for external release. Use
`startDispose`/`start-dispose!` for private cache/stdout owners. Active public dec
rejects before mutation. No callback runs on a Java recursive interpreter stack,
inside public dec, or as implicit close cleanup.

Authority is Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, original IR
and the pinned runtime primitive behavior. The exact 60-row static fixture
closure is [recorded separately](../test/fixtures/java-task-sync-runtime/README.md).
It includes metadata for unsupported async operations; fixture presence is not
execution support. This implementation and its small tests establish no full
image, kernel adapter, command declaration, imported Init or frontend success.

## Supported operations

| Operation | Behavior |
| --- | --- |
| Promise.new / result? | One runtime-created promised Task; retained result aliases have the same identity. |
| Promise.resolve / drop | First Some wins; losing payload is released before return. Dropping Promise resolves real None, completes synchronous propagation, then releases its Task owner. |
| Task.pure / ready get | Pure makes an ST ready Task. Get retains its value before consuming its Task owner. |
| Sync map / bind on ready source | Inline callback inherits current scope. Map wraps a ready Task; bind returns the exact callback Task, even if pending. |
| Pending sync map / bind | Own callback/source, register a nonowning dependency and return pending. Bind preserves outer identity while forwarding a returned pending Task. |
| BaseIO sync mapTask / bindTask / original chainTask | One counted keepalive owner survives discarded outputs, including pending bind forwarding, until final callback completion. |
| State / cancel / checkCanceled | Promised or running=1, waiting=0, finished=2. Cancel is a flag; source cancellation propagates at finish. Inline callbacks inherit scope. |
| Original CancelToken / result! | Execute the genuine guest bodies. onSet completes during set before its Ref flag becomes true. Some extraction transfers its payload. |

Only sync=true and canonical ordinary priorities 0..8 are admitted in this
profile. Async dependencies, spawn and BaseIO.asTask reject before native input
claims. Pending Task.get/IO.wait reject the unsupported blocking path rather
than inventing a value or parking a context. Option.getOrBlock! None reports the
unsupported panic/blocking path. No pending Task/Promise graph importer,
persistence grammar, executor, queued context, active Promise import or arbitrary
native FFI support is added. Pending values are constructed by this runtime.

One narrow native leak boundary also rejects terminally: a running pure bind
has already deactivated itself, then its callback returns a still-pending Task.
Pinned task_bind_fn1 installs a forwarding closure even after m_deleted, while
run_task's deleted/null-result path frees the task implementation without
releasing that new closure (object.cpp:744–751, 892–934, 1242–1270). Java preserves
the owned pending return in the action and rejects before forwarding,
registration or release. It neither resurrects the outer Task nor silently
runs cleanup effects absent from that native leak. This can occur through
ordinary concurrency or reentrant finalizers; it is not restricted to unsafe
Host code. Normal map deactivation, ready bind results and BaseIO keepalive
remain supported.

## Ownership and control

Ordinary Node fields remain owning. A runtime Task has VALUE plus two native
wrapper-capture slots; map orders captures [callback, source], bind orders
[source, callback], forwarding owns [nested source]. Promise owns RESULT.
Private absent slots are never guest null values. TaskMetadata contains only
kind, branch identity and primitive state; it owns no guest values.

TaskRecord, registration lists, detached batches and scope links are NONOWNING
in guest RC. Keepalive is a separately counted Task credit. Last-owner pure drop
unlinks its registration and releases its capture batch without running the
callback. A running deactivated map finishes its committed callback and discards
its result. Retired records are removed; no historical task registry is kept.
Detached registrations retain membership/backpointers so an earlier LIFO callback
can delete a later entry. Nested propagation completes depth-first.

RuntimeAction is private engine ownership/control state, outside NodeMetadata.
It reserves a result receiver slot, records exact Function/PreparedBody control
through the existing continuations, and saves operands/output and native suffix.
It invents no guest Function. Generic AP handles prepared, intrinsic, PAP,
oversaturated, CodeRequest and HostRequest callbacks. Stage fields identify moved
owners; stale argument/output aliases are diagnostics, not additional RC credits.

Ordinary decrements and quiet destruction complete inline using reusable scratch
with no per-node continuation allocation. Ready Task retirement tail-drains its
sole value before the enclosing zero-shell queue. At an effectful Promise
boundary the scratch is promoted into a forkable release action BEFORE dispatch.
Generic fields are decremented ascending as a full batch before zero shells are
visited LIFO. Promise propagation and its later RESULT release remain distinct
native boundaries. There is no thrown suspension sentinel.

Native actions preserve ST Ref.set DEC-before-store, MT/persistent exchange
before DEC, Array.pop size reduction before DEC, Array.set DEC-before-replacement,
and replicate(0) payload release before publishing the empty output. A captured
Ref is transitively marked MT by task allocation. A callback can change that
Ref again; the outer setter does not replay its earlier store after resumption.
Destroyed-shell access rejects rather than reproducing native memory unsafety.

First publication marks the value graph MT. Task allocation marks callback
captures/source and starts its own header MT. Duplicate resolution does not
mark its losing payload. Task.pure and sync-ready paths introduce no independent
mark. Marking remains separate from positive owner counts. Pointer metadata,
Array/ByteArray kind state and closure generation wrappers retain their existing
fork/uniqueness rules; no common Node field is added.

## Quiet release call-site audit

Only these local proofs admit remaining releaseQuiet calls. They are not a
transitive may-finalize prewalk or a public proof about arbitrary supplied values.

| Site | Local proof |
| --- | --- |
| Array COW / toList | All exported live elements retained before old container release. |
| Validated list toArray | Heads retained; remaining destruction retires ordinary list cells. |
| Shared/MT closure AP | All captures retained before old shell release; exclusive ST transfer uses DEL. |
| Ready Task.get / map / callback source get | Sole VALUE retained before Task release; no arbitrary payload loses its final owner. |
| Some extraction | Payload retained before wrapper release. |
| Nat/String/ByteArray helpers | Validated immutable carriers, character-list cells or zero-owning-edge byte payloads. |
| Recursive evaluator | Inactive profile only. |
| close | Active private owners already explicitly disposed; no implicit finalizers. |

IR DEC, external release/disposal, Ref.set, Array.pop/set, replicate(0), duplicate
resolve, Promise drop, task capture disposal and borrowed Host facade cleanup
instead use the resumable protocol. Active quiet-proof invariant failures retain
the current shell/cursor/worklist without dispatching a callback; inactive
legacy failure cleanup remains unchanged.

## Requests, fork and terminal failure

Reply validation stays before claim. A claimed Host reply saves its owned object
or raw scalar word while borrowed facade arguments are released one at a time.
The cursor advances only after its current release completes. Nested callbacks
may issue fresh Host/Code requests; linked completion records preserve outer
replies, cursors and owner dispositions. Host scalar reply bits are not converted
through OBJ storage. Owned Host arguments remain the adapter's explicit
consume/transfer obligations; retaining diagnostic argument views adds no owner.
No arbitrary FFI implementation is supplied by this profile.

One iterative fork memo copies guest Nodes, action chains, registrations,
detached batches, scopes, keepalive flags/credits, Host completions and code
activations, including dead queued shells. RC is copied, never incremented.
Runtime-created mutable Task/Promise values reject foreign branch owners at
ordinary ingress, request reply and fork roots. This extends their explicit
branch discipline; it is not a universal proof for arbitrary unstamped host
Node references.

Failure is terminal and retains unfinished owners/control. No rollback,
implicit finalizer unwind, failed-state fork, normal disposal or callback replay
is promised. In particular the narrow deactivated-bind boundary retains its
returned pending Task. Explicit action scratch has the same eight-million-slot
bound as the guest object stack; worklist growth is checked before final-credit
claims where feasible. Arbitrary OOM is terminal, not a resumable guarantee.

## Disposal and runtime quiescence

Root completion does not mean BaseIO keepalive ownership is discharged.
`taskRuntimeQuiescent()` is false during active control/requests/failure or while
keepalive work remains. Unresolved pure dependencies may still exist without
runnable effects; this observer does not promise every Task is finished.

Release external guest owners BEFORE private disposal. This is the host's
ownership precondition, not an inferred inventory of external aliases.
startDispose moves private cache/stdout owners into its action ledger. Retired
cache IDs are tombstoned and cannot replay initializers. A callback may first
initialize a genuinely new closed constant, even behind the sweep cursor;
repeated sweeps retire that owner and any recreated stdout root before success.
Persistent RC0 globals and ordinary guest RC cycles are not collected.

If unresolved BaseIO keepalive work remains, disposal parks in explicit
`waiting`: advance returns false, no Unit result is available, and close rejects.
The state can be inspected/forked. This tranche provides no external resolution
transaction while that disposal is parked; callers must arrange source lifetime
and resolution before disposal. It never reports a false quiescent close.

After completed disposal only diagnostics, the one Unit takeResult and
nonexecuting close remain supported. startRelease, start/invoke, inc,
makeClosure, installGraph/installProgram, finishInitialization and fork reject
before claims. Close also checks that no private owner roots were recreated.

## Bounded validation

The enabled focused suite currently has **39 tests / 366 assertions**, run in one
retained 256 MiB REPL, with no Init/full image. It covers genuine wrappers and
CancelToken/result! bodies; LIFO/depth-first registration behavior; deleting later
detached entries; keepalive/bind forwarding; scalar and object Host reply
ownership; missing-code, intrinsic/PAP/overapplication callback receivers;
release/Ref/Array native suffixes; first/duplicate publication marking; cancellation
scope and running deactivation; cache/stdout disposal; waiting and failure;
preclaim/foreign/admission fences; a 3000-task propagation fork; 6000-deep quiet
ready retirement; and 12000-record iterative control-copy models.

Existing inactive Host, Code, generation, root release, Array, Ref, ready map
and logical sharing suites were also run. Integration/full gate and real
sequential frontend probes belong to the root campaign after independent review.
Native oracle receipts remain separate evidence; a matching installed Lean
binary does not prove the historical producer executable or general async timing.
