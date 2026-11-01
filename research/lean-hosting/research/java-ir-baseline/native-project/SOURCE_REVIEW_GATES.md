# Source review gates for ordinary local projects

These are agreed implementation and release requirements, not implemented
capabilities or runtime acceptance. They refine the
[general project plan](GENERAL_PROJECT_PLAN.md), the
[Java API proposal](JAVA_API_DESIGN.md) and the
[compact startup proposal](../startup-evidence/PLAN.md). Existing fixed-profile
and isolated runtime receipts remain bound to their exact sources/cohorts.
This documentation launches no compiler, JVM or guest execution.

## Sequence and first supported profile

Land reviewed initializer publication, ByteArray.get!, checked entry evidence
and existing JVM compiler packaging prerequisites independently. Then proceed:

1. Genuine compact startup evidence, its module/action ledger and bounded
   portable JDK entropy capability. Establish ordinary Init readiness with the
   actual Random action, actual global publication and normal owner retirement.
2. Generic bounded local-project artifact/compiler and one reusable Project
   engine: exact native checked entries, complete selected code/startup closure,
   capability admission, persistent globals, Nat/String codecs, cooperative
   limits and validated failure lifetime. Preserve the fixed tutorial profile.
3. Public Java facade and jar-only consumers: ordinary dependency resolution,
   no checkout paths, Python, Clojure CLI, runtime javac or manual exporter step;
   verify both source-build and precompiled-artifact deployment modes.

The first project profile is trusted local source, acyclic ordinary imports and
Init, data-only project configuration, no arbitrary Lake scripts/package
fetching/plugins. Native Lean checking/compilation is the explicit authority.
Compilation can execute native metaprograms and compile-time IO; this profile
is not a security sandbox. Main IO Unit and closed monomorphic unary Nat/String
entries are requested signatures, established by native CI/DefEq evidence and
the original selected callable, never by caller descriptors or ABI alone.

The default native runtime path must not load the full guest ModuleData graph,
recheck Init proofs, initialize a hosted frontend or fetch Mathlib. Optional
kernel/store integration is a separate explicit service and cohort.

## Portable entropy: real bytes, truthful guest errors

Choose a documented portable JDK entropy provider for v1. Its bytes are genuine
entropy under that provider's contract. Do not claim exact Linux /dev/urandom,
POSIX errno or native source/error parity. Record the actual algorithm/provider
and implementation policy in the runtime capability descriptor; do not serialize
the generator's internal state or treat an algorithm label as source attestation.

The admitted operation must implement the actual original IO.getRandomBytes
Header/ABI and return an engine-owned guest ByteArray inside a genuine IO result.
No arbitrary host byte[] becomes a guest value, no graph-import factory is used
for each result, and no supplied accepted/type flag authorizes completion.

The transaction order is mandatory:

1. Validate actual engine/request/Header/token/ABI, ownership phase and canonical
   unsigned USize. Compare unsigned size to the configured cap before narrowing
   to an int; a negative Java long can represent an enormous unsigned request.
2. Preflight capacity and allocation/effect journal before reading entropy.
   Publish every output/claim slot needed for failure custody. A valid zero-size
   request creates the genuine empty guest ByteArray with zero logical size and
   performs no entropy-provider call, lazy seeding or RNG construction effect.
3. For a positive request, publish EFFECT_STARTED before constructing/invoking
   the provider. Read into a private bounded buffer; then copy/fill owned engine
   ByteArray storage under the reviewed engine factory and IO-envelope codec.
   Caller mutation must never change an issued guest value. A provider cannot
   manufacture Node metadata/tags or choose an unrelated pending request.
4. Commit the same actual completion once. Failure after the read retains its
   actual output/owner journal; it never repeats the entropy read automatically.

Expected provider failures become actual IO.Error.userError with bounded,
truthful operation/provider/error-class details. No invented POSIX code,
filename, errno, ENOMEM, successful empty buffer or raw String in place of
IO.Error. The error constructor/layout needs source-bound evidence or a reviewed
engine codec; its printed name is not a tag/layout proof.

Use a closed reviewed exception classification: documented provider failures
(for example ProviderException or an adapter's explicit EntropyFailure) may
become userError. Invalid configuration is a preflight/configuration failure.
Programming invariant failures are not provider IO errors. Cancellation,
InterruptedException, ThreadDeath, LinkageError and VirtualMachineError/OOM
remain host failures, with interruption preserved and real custody retained.
Never catch Throwable and translate everything into guest IO.error.

JDK provider internals need not expose a close method. Dispose actual tracked
resources according to their real API; do not claim that dropping SecureRandom
closed hidden OS resources or unwound a pending provider call. Any injected
provider that does own a closeable resource needs explicit scoped ownership.
No readiness, close or abandonment while an entropy read is still executing.

Tests must distinguish zero/no-effect, unsigned over-cap/no-effect, successful
8-byte seed/action/global reuse, copied-buffer isolation, expected provider
failure/userError, wrong token/request/engine, duplicate completion, and host
cancellation/VM-failure classification. Deterministic test entropy is explicitly
labelled and never the default production source. Real entropy tests assert
shape/ranges and no second initialization, not fixed random bytes.

## Atomic Nat operations and cooperative resource claims

Host quanta cannot interrupt a single unbounded Java BigInteger operation.
Codec input limits and a final result-size check are insufficient. Before
public generic execution, enforce bit/allocation and work limits inside the
actual atomic Nat primitives, starting with multiplication, power and shifts.
Audit all other growth-producing Nat/Int/string/array primitives as part of the
admitted runtime profile; fixing three operations is not a global memory proof.

- Validate operands and overflow-safe bit/work upper bounds before allocation.
  Do not multiply Java ints/longs to estimate size and then check an already
  overflowed product. Conservative bounds can explicitly refuse work, but must
  not truncate a Nat, wrap arithmetic or return a fabricated result.
- Nat.mul charges an operand-size-based work estimate and bounds the product
  allocation before BigInteger.multiply. Account for any bounded guard margin
  and JDK temporaries; do not describe a result-bit cap as a hard JVM heap cap.
- Nat.pow retains the pinned source's exponent admission and exact zero/one
  semantics. Bound result size/work before the first multiplication. Repeated
  squaring checks cancellation/deadline/work and size before every multiply or
  square, polling between steps. It cannot run unchecked until the final result.
- Left shift bounds shift magnitude plus input/result bit extent before
  narrowing or allocating. Right shift handles a huge unsigned Nat shift using
  comparison before narrowing. Preserve source zero/identity cases and the
  existing distinction between malformed inputs and profile-size refusal.

Budget refusal/cancellation preserves the existing invocation's real owner and
failure state. It does not restart the operation in a native executable or a
fresh engine. These are cooperative work/allocation guards, not hard heap,
wall-clock deadline or preemption guarantees. JDK/library calls can occupy the
thread until they return. Public documentation must retain that qualification.

Tests need exact boundary results, estimate overflow, huge exponent/shift
rejection before allocation, deterministic cancellation between pow steps,
no partial result publication, and correct failure custody. Native comparison
tests establish arithmetic values for admitted cases; they do not measure a
worst-case memory/cancellation guarantee.

## Failed Project close and task-free GC abandonment

Current Engine.close rejects active/failed explicit execution. Do not remove
that guard, clear frames or flip closed/disposed bits and call it guest cleanup.
The public Project lifetime needs an independently reviewed restricted-profile
GC-abandonment path for those cases, in addition to normal owner-aware close.

Eligibility is an actual private issuer check after advance/provider calls have
returned: task-free engine; no pending/running task or Promise callback; no
external native/FFI handles, borrowed mapped arenas or source regions; no escaped
guest Nodes; no unsettled tracked host operation/resource; and a profile whose
remaining graph consists only of managed JVM values/closures/refs/byte storage.
The caller cannot supply a safe-to-abandon Boolean. Settled host resources must
be evidenced by actual ownership journals, not journal status strings alone.

For an eligible failed/cancelled branch:

1. Make the Project and all its handles unusable; serialize with calls/close.
   Prevent replay, new roots, fork or another entry on that branch.
2. Complete actual tracked host-resource retirement where known and required.
   Uncertain or active resources remain quarantined; do not label them settled.
3. Copy bounded value-only diagnostics (stage, Names, counters, limited messages
   and relevant status), without exposing raw engine/Node/owner-packet aliases.
   Throwable causes/ex-data and registry values must not retain the abandoned
   engine through hidden backreferences. Preserve the true error category; a
   bounded diagnostic projection is not an invented successful unwind receipt.
4. Drop ALL issuer references to the engine, frames, journals/outputs and their
   graph. This is host-reference abandonment allowing JVM GC, not guest DEC,
   finalizer execution, normal engine close, rollback or proof that GC ran.

Normal idle retirement should still release/take known results and close
normally. Close remains idempotent at the public scope. A failed branch cannot
be reused merely because immutable code survives. Loading a separately requested
new Project from the same cache is a distinct operation, never automatic replay.
Profiles with callbacks/external resources require actual supported teardown or
retained quarantine; the initial abandonment policy must refuse them.

Acceptance needs failed and cancelled active frames, a completed owned result,
provider failure after an effect, repeated close, handle invalidation, no guest
unwind claim, no weak-key/value retention cycles and bounded diagnostics without
engine retention. Reachability tests supplement actual resource/lifecycle tests;
they cannot establish that unknown native finalizers were discharged.

## Public fork is deferred

Prefer omitting public fork in the first release. If exposed later, restrict it
to actual READY, idle, task-free, quiescent Project issuers that own all guest
roots, with no outstanding result/host packet/provider operation or escaped raw
guest value. Validate the complete root set, not caller-supplied sample roots.

Use the existing eager graph/stack copy honestly: cost is O(reachable graph plus
allocated stack capacity), not a cheap persistent-store fork. One memo must
remap globals, streams/defaults, captured values and aliases together. Clone the
actual entered/succeeded module ledger, initializer attempts and the guest
IO.stdGenRef/StdGen state. Do not rerun initialization or request another startup
entropy seed. Preserve source/version/lease and branch pointer identity rules.

Cloning guest PRNG state does not clone undocumented JDK SecureRandom internals
or promise identical future external entropy/IO. Future explicit entropy reads
remain real effects under a separately defined provider policy. Fork failure
must not partially publish a child or duplicate owner authority. Require exact
alias/RC/ledger/random-state and no-reseed tests before any public claim.

## Separate cohorts and ordinary packaging

| Cohort | What it binds | What it does not establish |
| --- | --- | --- |
| SDK/runtime | Actual runtime Class/JAR, native registry and exact ABIs, codecs, provider/lifetime policies, schema support | Native source checking, kernel proof checking, matching arbitrary cached Headers |
| Native toolchain | Trusted installed Lean version/commit/target, executable identities and declared installation mutation guards | Full cryptographic attestation of every sysroot file or Java execution parity |
| Producer | Source capture/DAG/config, helper source/binaries/options, entry/startup/raw output hashes, orchestrator/schema | Runtime initialization already executed or caller signature truth |
| Optional kernel/store | Exact store format/branch/Lean cohort, immutable content roots, checker/loader and lease policy | Matching guest ModuleData/frontend state, native IR initialization or automatic proof replay |

Portable artifact bytes are admitted under a supported SDK/ABI profile. Prepared
Program/Header caches bind the actual runtime Class/cohort and SourceBinding;
never deserialize them across classloaders because version strings match.
Native entry/startup facts bind the exact producer/toolchain/source inputs.
Kernel stores keep their own proven lazy loading/fetch protocols. Do not build
a second kernel DB or use a stored verified flag as a guest association proof.

Lean.open configures lightweight services. It does not fetch Mathlib, hydrate
full Init, replay proofs, boot a hosted frontend or run a native compiler merely
because a kernel component is available. Explicit kernel/store opening can
reuse the existing lazy loader/fetch API, with an explicit offline/download
policy and actual published store index. Default native-project execution does
not require a full Init kernel store or mapped ModuleData arena.

An ordinary Java Maven/Gradle consumer must receive actual Java classes and
required transitive runtime dependencies. No Python, Clojure CLI, source checkout,
runtime javac or per-call classloader. Source build can use one configured
official toolchain plus a bundled/resolved independently pinned platform helper.
Precompiled artifact/resource loading can avoid a native toolchain entirely.
Verify extracted helper bytes and private cache/atomic publication. Linux prlimit
and process-monitor assumptions are implementation/deployment requirements,
not an unqualified cross-platform SDK promise. Jar-only tests must establish the
chosen supported JDK/platform and source-resource closure with checkout sources
absent, including this compiler's implementation-source authentication.

## Review evidence required before release

Each stage needs exact source/binary/data receipts, original native comparison
where relevant, meaningful negative models and actual integrated execution in
one admitted runtime cohort. Keep compile cold/cache-hit, startup, repeated-call,
error/cancellation and close/abandonment measurements separate. Repeated calls
must reuse the Project engine/globals and start zero compiler processes.

Do not combine independent successes into an unrun end-to-end claim. The existing
tutorial and isolated typed bridges remain useful evidence, but do not establish
ordinary Init startup, generic local discovery, public failure lifetime, fork,
jar-only deployment or hosted/kernel matching. This plan commits requirements
and review decisions only; actual implementation and release status must come
from the subsequent source and runtime gates.
