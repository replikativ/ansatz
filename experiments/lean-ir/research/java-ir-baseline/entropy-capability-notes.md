# Portable JDK entropy capability: review checkpoint

Base: byte-get landing a2b7ee2d, exact tested Java9a3af598cf1168d15ba67b5dac49a302028329d885d18b91df97344baf37430e.
Source implementation review checkpoint; runtime/model gates pending. No worker JVM/native processes. This is the
portable JDK profile approved by root, not POSIX errno/device-source parity.

## Proposed narrow public research API

- `EntropyCapability.secureRandom(algorithm, providerName, maximumBytes)` creates
  and privately owns a genuine JDK SecureRandom once, using the explicitly
  configured installed provider (or a documented default-factory overload).
  Capability metadata records profile `portable-jdk-entropy/1`, actual algorithm,
  provider name/version and allocation bound. Do not retain a caller-supplied
  mutable/extensible SecureRandom reference or silently change algorithms.
- `EntropyCapability.deterministicForTesting(bytes, maximumBytes)` clones the
  supplied bounded pattern. Its profile is explicitly test-only; it never claims
  real entropy. Request size must match the test pattern (zero remains free).
  A separate test failure source can throw only the reviewed expected-source
  failure class; it cannot construct arbitrary guest Nodes or manufacture success.
- `installEntropy(capability, actualEntropyHeader, actualUserErrorHeader)` configures
  one engine once, while it is explicit, open, fresh/instruction0, idle, task-free,
  without a pending initializer, call, result or host/runtime action. This is
  before module startup. Both canonical registered Headers must be same-source;
  the error helper body must be ready. Metadata access is read-only and returns
  immutable scalar provenance, not the SecureRandom object.
- An internal attempt journal is visible through a small immutable diagnostic
  snapshot (stage, requested unsigned size, effect-called/completed booleans,
  owned slot dispositions/counters), plus a guarded borrowed owner packet if
  necessary for failure diagnosis. It is not an arbitrary close/retry API.

Native extern is `lean_io_get_random_bytes` from exact original row
afc15888b42a236a70bd422ced2bacca2d0808810d0ee7540495985d7ff9c368:
owned usize, owned void→object. Add one new distinct intrinsic558. No HostExtern
registration upgrade, general Node factory, graph-install slot or guest callback
export is required. Validate the actual world placeholder and unsigned USize
against the configured existing ByteArray bound before allocation/effect.

## Actual error codec evidence

The original `IO.userError` declaration was found by bounded catalogue lookup,
not by constructor-order guessing. Row SHA
53b224c8fa037b144260872e3b14878aff86dbb61b598e1ea49f991dabc1fb6b has
owned object→tobject, body `ctor_18[IO.Error.userError] message`, one object field,
zero scalar bytes/usize fields. Freeze the raw original row as a fixture and
require the actual same-source canonical Header/ready body at installation.
The runtime codec's fixed constructor layout will be justified by this exact
original IR and tested against executing the genuine helper on the same message.
IO.ok/error envelopes use the actual EST.Out.ok/error descriptors in original
Random action526bcf3a5d70f4d1ec594fe7bab187be148466c44e4ca173d1739bf04723bb30
(tag0/tag1, one object field, no scalar bytes). Freeze the relevant original
evidence, and compare constructed errors through original checking/projection
or the actual original constructor call. A string alone is not an IO.Error.

Only an explicit expected entropy-source failure maps to IO.error(userError
boundedMessage). For the JDK implementation, wrap only a known provider-source
failure (`ProviderException`) from the one nextBytes call. Invalid profile or
arguments, interrupt/cancel, ThreadDeath, LinkageError, VM errors/OOM, unexpected
runtime exceptions, invariant/ownership errors remain terminal host failures.
Check interruption before effects and after callback return; interruption never
becomes a successful/empty entropy result or an automatic repeated read. Error
messages are bounded and portable, with no fabricated errno/POSIX claim.

## Integration with the actual instruction machinery

Use a dedicated RuntimeAction/EntropyAttempt, not the current synchronous generic
intrinsicExternal path. Current `actionPrimitive` is mostly gated on TaskRuntime;
entropy must be recognized for the task-free explicit engine used by
startInitializer. Legacy inactive entropy execution should reject clearly; the
first capability supports explicit driver only.

`enterNative` validates source/Header/capability/ABI/size/world/thread and creates
the action. It publishes the actual argument/custody journal before any source
effect. `stepAction` dispatches a new ACTION_ENTROPY, using ordinary finishAction
to deliver the owned result into the original root/FAP continuation. No synthetic
guest start or second result channel. Named initialization then uses the genuine
startInitializer/completeInitializer transaction already implemented.

Proposed stages (host allocation failures are terminal and leave previous stages
and all already published guest roots in the action):

1. VALIDATED: size/world/profile/ABI/interruption preflight; unsigned `long` values above
   the bound reject, never narrow into a negative/small int. No source call.
2. PREPARE: allocate the private ByteArray with exact size/capacity and publish its
   owned slot immediately; allocate/publish the actual success wrapper holding
   it; allocate the host buffer. All are ready before requesting entropy. If an
   allocation fails, retain published roots and fail the engine; no read occurred.
3. EFFECT_PENDING→EFFECT_CALLED is committed before nextBytes/fill. Exactly one
   source call is permitted. Size0 bypasses the source entirely and returns the
   already initialized empty ByteArray wrapped in IO.ok.
4. EFFECT_RETURNED: copy host bytes into private guest scalars. The source never
   sees the guest buffer. Record completion before output publication; later
   failure does not repeat the call. Clear host buffer references when safe.
5. EXPECTED_ERROR: bound the expected error message, construct/publish real
   userError and error wrapper. Retire the known success graph (ByteArray+wrapper)
   only once, with explicit slot dispositions; retain both graphs if construction
   or retirement fails part-way. These nodes have no callbacks/finalizers, so a
   quiet release is suitable, with stage set before it. Unexpected source throws
   preserve the success graph, not an invented IO error.
6. READY→DELIVERED: latch owned output in the action before finishAction. If
   finishAction/application delivery fails, failedRuntimeAction retains the
   attempt and output. There is no public rerun or automatic cleanup/unwind.

Each advance quantum remains cooperative. The one JDK nextBytes call can block;
this design cannot honestly promise preemptive cancellation or a hard deadline
inside that provider call. Allocation/preflight/copy/completion checks can observe
interrupts around it. Public release guarantees must reflect this limitation.

## Fork and lifecycle decision

An EntropyCapability is a deliberately external shared service, not guest state.
Its immutable descriptor/private source reference may be shared by an idle fork.
JDK SecureRandom is thread-safe; sibling future calls consume independent draws
from the same external source, not cloned RNG state. The deterministic test
pattern source has no advancing private cursor, so sharing has explicit semantics.
Branch counters are copied as historical counters and then grow separately. No statistical independence is claimed for shared-generator draws.

When entropy is installed, first profile permits eagerFork only at a healthy idle
boundary with no pending entropy action/journal/result/initializer. Reject a
paused/running entropy-capable engine before child construction; do not attempt
to add EntropyAttempt to generic ForkCopy. Copy only the capability reference and
completed historical counters, never an in-flight effect or mutable host buffer.
This narrows forks for this opt-in capability; engines without it keep their old
fork behavior. Each EntropyAttempt captures its publication Thread and guards every
dispatch/effect/completion against that thread. No configuration-thread affinity
is imposed at idle; a serialized idle handoff or child may start its next attempt
on a different owner thread, consistent with the existing exclusive-engine contract. ForkCopy already clones initialized constants/reference graphs;
child inherits the actual stdGenRef value/state and initializer-attempt bits.
Do not reseed or rerun Random's initializer when copying that state.

Normal idle close clears the installed engine reference after real result/global
owner retirement; it does not close a shared SecureRandom service or siblings.
Pending/failed entropy custody cannot be passed to close and called discharged.
No callback-capable public Project abandonment API is being introduced here.

## Proposed bounded validation

No worker JVM/native. Root compiles once and uses its retained REPL:

- Exact original extern ABI and wrong borrow/result/world/unsigned-cap refusal.
- Missing/duplicate/late capability and foreign/noncanonical error Header refusal.
- Zero request yields true empty ByteArray, no source call; deterministic8 bytes
  match exact logical size/capacity and owned IO.ok layout.
- Caller pattern and source-retained host-buffer mutations cannot change issued
  guest bytes; source cannot access guest storage.
- Expected ProviderException produces actual source-equivalent userError/IO.error;
  generic runtime/VM/interruption failures stay terminal with journal custody.
- Fault injection before read, after read and during completion proves one effect,
  preserved owned result and no repeated source call. OOM cannot be caught and
  misreported as a harmless native IO error.
- Idle fork shares only the external capability, clones initialized guest Ref/
  stdGen state and counters; pending/running forks reject before allocating child.
- Genuine private Random initializer uses deterministic00..07, publishes the
  expected StdGen reference once and reuses the same global identity without
  another source call; real JDK entropy is a separate nondeterministic shape gate.

Review requested before implementation: explicit-only action integration;
source-backed fixed error codec; expected ProviderException mapping; shared
external service with idle-only forks; and the cooperative nextBytes boundary.

Final review additions: an explicit monotonic everStarted flag, preserved by forks,
replaces instruction-count freshness. task-free prepareExplicitApply prevalidates
entropy before closure ownership changes. Engine pendingEntropy retains attempt
and output across finishAction; commit hooks distinguish owned, transfer-started
unresolved and delivered aliases. Successful history retains scalar counters only.
