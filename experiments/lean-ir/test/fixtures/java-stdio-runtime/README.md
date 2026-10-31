# Opt-in synchronous logical-thread stdio

This profile adds five public stdio natives to the existing captured stdout path.
It does not implement host filesystem IO, workers, asynchronous tasks, handles,
UTF8 conversion, or heartbeat substitution. Native IDs545–549 are respectively
IO.getStdin, IO.getStderr, IO.setStdin, IO.setStdout and IO.setStderr. Private550
implements captured-stderr putStr;551–552 remain unused. Existing getStdout24 is
unchanged in ABI and retains its legacy root/count behavior without installation.

## Original contract and source evidence

Lean pin819816b2e0a3bf405af45ae5c7af2491d8f5bee6 runtime/io.cpp112–158 uses
process defaults and OS-thread-local object_ref slots. runtime/thread.h204–216
initializes each slot lazily from its default and registers a thread finalizer.
A getter retains a return occurrence; a setter takes the incoming owner and
steals the old slot owner directly into the return. All return Stream DIRECTLY
(BaseIO), not IO.Result. Raw getter ABI is `[void owned] -> object`; raw setter
ABI is `[object owned,void owned] -> object`. Original boxed facades replace only
world void with tagged. The actual21-row fixture preserves those twelve original
raw/boxed declarations plus the original Stream.ofBuffer constructor, two closed
method values and six original method wrappers. No body is synthesized or edited.

The collector hashes the actual accepted index stream (120,853,740 bytes /
375,258 typed declaration pairs), requires all21 exact Name/hash memberships,
then authenticates each original CAS blob. SQLite is only a candidate accelerator.
Source/index/blob hashes and removal of only top-level pretty are recorded in
provenance.json. Regenerate with `collect.py REVIEWED_ROOT LEAN_REPOSITORY`.

Native synchronous pending callbacks execute on the resolver's thread; ready
callbacks run on the registering thread (object.cpp787,1211,1273). Task completion
has no stdio reset/cleanup. Current Java logicalSynchronous forbids spawn/asTask and
sync=false. Consequently one branch-level logical-thread context, shared by all
supported guest callbacks, is the admitted domain. No slot is keyed by currentTask
and no task execution/finish path acquires, restores, or retires stdio owners.

## Actual default-input witness and installation

The trusted caller creates an initially empty real Buffer (data:empty ByteArray,
pos:Nat0), a real Ref to it, and executes the authenticated original
`IO.FS.Stream.ofBuffer`. This must happen on a FRESH child after pristine seed
fork; construction executes guest instructions. It can happen after finalizer and
startup, avoiding source receipt/startup drift. Never run it against an instruction0
seed that is meant to remain pristine.

At an open idle boundary call:

```clojure
(j/install-stdio-defaults! current-basis engine actual-ofBuffer-Header stdin-stream)
```

This call BORROWS the stream. It does not invoke any guest code. Installation
checks the actual registered original constructor Header (pinned Name/SHA), each
method's actual same-SourceBinding pinned original Header, its closure generation
and boxed ABI, the shared Ref captures, and actual empty Buffer layout/data/pos.
A bounded iterative readonly traversal includes persistent rc0 subgraphs and
checks live storage/kinds, rejects Task/Promise/opaque/native-handle kinds, and
checks node/edge limits before any retain or publication. All source/index/raw CAS
and CodeReceipt authentication remains the trusted source adapter's responsibility;
Header SHA fields alone do not prove that authentication or issue source authority.
This runtime boundary uses existing pointer/generation/Node discipline, not a new
universal ownership seal for arbitrary unstamped foreign ordinary Nodes.

The source-proven data-only factory in the tiny tests uses the original Buffer
and Ref layouts with an actual imported empty ByteArray; then executes the genuine
constructor body. It is not a replacement of Stream.ofBuffer or its methods.
Only constructor/closed/stdlib boxed bodies needed for construction are materialized;
method wrappers stay authentic callable Headers. Running original buffer reads,
getLine or writes still needs their full admitted native/code dependency closure.
Parent integration must run the actual withIsolatedStreams path after that closure
is combined. Direct stdio unit tests do not claim that path already succeeded.

Installation acquires ONE stdin default owner. The caller keeps its input owner
and must release that external occurrence before engine disposal. Existing
stdoutRoot is the stdout default owner; an independent stderrRoot is created on
first use. Current slots lazily retain one default occurrence. A getter retains
one more returned occurrence. A swap takes its argument owner and returns the old
slot owner with no inc/dec, including identity swaps. Overflow/world/layout checks
finish before native owner publication. Setters reserve each known identical
default/current occurrence (including cross-channel aliases) and require a
separate incoming owner beyond them; persistent rc0 is exempt. The guard runs
at raw entry before frames and again at the internal native FAP/AP site. This is
a narrow known-credit defense, not a universal heap ownership ledger. Defaults/current/external aliases count
separately; persistent rc0 remains persistent. An uninstalled profile refuses new
channels and swaps explicitly, while legacy captured stdout still works.

Private stdout/stderr defaults support flush, putStr and isTty only. Read, binary
write and getLine retain the existing explicit unsupported sink profile. Genuine
original Stream.ofBuffer methods stay genuine guest closures and are never routed
through those synthetic sink operations. Captured stdout and stderr text are
separate; replacing current streams does not mirror output into default sinks.
No System.in/out/err or physical resource capability is used.

## Fork, mutable defaults and retirement

One ForkCopy memo remaps all default/current roots, saved previous streams,
continuations, refs, captures, pending actions and explicit external roots.
Default/current aliases remain aliases in the child; mutable graphs and output
text stay independent across branches. RC counts are copied without invented
credits. Task identities do not select the context; a callback registered underA,
resolved underB, and installingC seesB and leavesC visible to its caller.

Active runtimes retire current-slot owners and closed-cache owners resumably,
recording each old occurrence before clearing its slot and claiming release.
Callbacks may recreate earlier current slots/caches. Repeated sweeps continue
until these callback-producing roots and task keepalive work are quiescent,
while ALL process-default owners remain available. No task-finish cleanup exists.

Before the first default owner claim, all actual default graphs are revalidated
readonly in that same native step. Each subsequent default graph is checked again
at its own claim. Only callback-free defaults are supported: private sink closures
and the configured ordinary Buffer graph. Unsafe Ref mutation to Task/Promise is
caught BEFORE any default root transfer if present at that first sweep. Failure
retains the actual default slots and runtime-action journal; no teardown, template
reset, fake finally, or hidden borrowed seed owner is invented. Legal guest
execution cannot interleave the validation/claim because this profile is synchronous
and the native phase does not yield between them. Ordinary typed Buffer updates
retain their position/data and do not involve callback-bearing values.

Arbitrary callback-bearing CURRENT streams are supported by the existing release
runtime. Arbitrary callback-bearing DEFAULT streams are deliberately unsupported:
their process-default lifetime would require a distinct leased owner surviving
logical-thread teardown. Close requires every owned default/current/cache root
retired. In inactive runtimes only callback-free/no-task quiet close is available.
Failed explicit execution remains escrowed rather than automatically unwound.

## Verification

`stdio-checks.clj` defines thirteen tiny test families: exact source/ABI evidence,
legacy opt-in boundary, readonly rejection of callback-bearing defaults, lazy
counts and identity swaps, borrowed same/cross-channel/lazy-slot alias refusal
and original boxed-FAP bypass refusal, capture separation/current redirects, source/layout/
overflow preflight, malformed native swaps, fork/saved-owner aliases, pending
resolver-time callback and persistent callback swap, callback-created retirement
plus paused fork, and post-install Ref mutation rejection before default claims.
They use actual original Headers and constructor bodies, actual Ref/ByteArray
storage and the actual existing synchronous task/release machinery. The default
Buffer's unadmitted UTF8/read/write frontier is not stubbed.

Load after existing byte-array and sync-task check definitions, then invoke
`(java-ir-stdio-checks/check! new-basis)`. Both control/explicit modes and the active
synchronous task profile are exercised where applicable. No large image is loaded;
three tiny source-created Streams suffice per fixture. Intentionally failed
explicit tests keep their real failed state and do not fabricate cleanup.

The author ran index/CAS/source/delimiter/path/diff audits only; no agent JVM,
javac or native process. Root must compile a frozen immutable jar, run focused and
full gates using an isolated basis, then combine the separately reviewed UTF8 and
heartbeat units before actual original realization/withIsolatedStreams acceptance.
Old runtime cohorts and pristine seeds remain valid and unmodified.
