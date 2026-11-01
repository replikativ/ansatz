# Ready Task.map on the explicit continuation stack

The experimental Java interpreter supports the original six-argument
lean_task_map ABI and genuine Task.map boxed wrapper, using pinned Lean 4.33.1
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Its profile is the native
no-task-manager branch: obtain an owned ready-task value, apply the callback once,
and transfer the complete result into a fresh ready Task. Both sync values use
that branch. A Task-valued callback result is wrapped again, without flattening.

The raw parameters remain erased α, erased β, owned tobject callback, owned object
Task, owned tobject priority, and uint8 sync, returning object. Erased values must
be canonical zero; sync must be 0 or 1. Priorities must be immediate nonnegative
Long values, including 0/8/9 and the supported immediate maximum. Their value does
not schedule work in this profile. Heap-sized Nat priorities reject before owner
transfer; the implementation does not model native unboxing of heap values or
claim a broader arbitrary-Nat priority extension.

Preflight checks the actual closure's generation, boxed parameter ABI and direct
callability, the private readyTask kind/shape and live value, and the known local
input/capture/field owner occurrences. It does not audit the full heap. A callback
that remains underapplied produces a partial closure without forcing its body.
A direct full callback requiring code or a Host effect rejects in recursive mode
before consuming map inputs. Recursive mode otherwise uses its existing internal
apply path; it never switches drivers or polls a suspension.

Explicit execution installs one private runtime frame with APPLY and WRAP states.
Its active Function is the actual Task.map declaration. Its separate prepared
layout never enters an append-only Program slot, and imported IR cannot name the
private opcodes. The ordinary continuation saves the exact guest or runtime
callerPrepared. The two private states each count as one dispatch instruction;
advance(0) executes neither. APPLY charges the ordinary call budget before get.
Nested maps use explicit frames and yield between dispatches, with the existing
stack/depth limits; they do not invoke callbacks on the Java call stack.

APPLY increments the payload before decrementing the input Task, then sends one
owned argument through generic applyExplicit once. Partial results, immediate
intrinsics, ordinary bodies, CodeRequest and HostRequest all deliver their full
result to map's result slot. WRAP validates that result, allocates the ready Task,
and transfers its result field without another retain. Ordinary return restoration
then delivers the Task to root/FAP/AP callers. Outer AP surplus is applied after
WRAP, so applying a Task rejects rather than accidentally applying a callback's
returned closure.

All suspended guest references stay on the ordinary objects stack and share its
fork memo. Slots 1/2/3 hold callback/input Task/result; slot 4 records get's retained
payload; slot 5 is a borrowed capture snapshot and slot 6 is AP's argument vector.
Neither snapshots nor stale diagnostic aliases acquire owner credits. Numeric
slot 7 records progress: retained payload (1), task release started (2), task
consumed (3), callback AP started (4), callback published (5), and wrapped (6).
The temporary slots clear after successful AP publication. Their prepublication
contents remain available on failure; complete arbitrary guest-failure RC cleanup
is still unsupported. No NodeMetadata object contains guest references.

Forks before APPLY, at callback code/host suspension and before WRAP preserve
control/layout identity and remap aliases through the same graph memo. Descendant
Program installation at existing safe boundaries leaves saved runtime layouts
intact. Invalid replies preserve the suspension; claimed failures remain terminal
and never repeat get, callback or WRAP. Active/failed explicit close still rejects.
No callback exception is converted into a ready error Task or a successful result.

The focused model suite covers original raw/boxed entry, wrapper PAP/AP, owner
aliases and rejected missing credits, unique/shared/persistent inputs, scalar,
closure and Task callback results, unforced underapplication, nested/self-tail
control, step budgets, sibling rejection, code/host fork/resume/failure, static
borrowed Host calls, Host-reply overapplication, and surplus ordering. A modeled
host mutation of immediate Ref payloads checks fork isolation; it is not a new
public Ref mutation API. [Original fixtures and provenance](../test/fixtures/java-task-map-runtime/README.md)
remain separate from the campaign's actual compiler/frontend continuation gate.

No worker queue, scheduler, Future, active Promise, pending Task import, spawn/bind, cancellation,
parallelism, exception-as-Task policy, general failed-execution cleanup or full
frontend acceptance follows from this change. Existing graph/provider defaults
and initialization phase remain unchanged.

Integration gate: the isolated Java 11 jar exits zero with 684 test executions /
20,924 assertions across 75 suites at 384 MiB. Independent source/continuation/
ownership review found no blocker. The real command-frontend probe now passes
the map in Environment.modifyCheckedAsync using a genuine mkEmptyEnvironment,
Options.empty, module Name and empty root array, copied with all external owners.

Its next dependency was the captured initialized linter option. The companion
extension imports/forks successfully at the same heap limit: 44 globals, 82,276
Nodes (four additional persistent constructors), unchanged 1,723 selected owner
credits, 134,561 scalar bytes and 2,726 Headers. The actual option default is true;
no substitute value or initializer replay is used. With that companion, the
prelude axiom command reaches 467 newly demanded bodies / 296,935 instructions
and stops at unsupported String.Pos.set. It has not published a checked axiom or
completed command elaboration. Pending Promise/dependency support remains a
separate logical-runtime stage; native no-manager mode cannot create Promises.
