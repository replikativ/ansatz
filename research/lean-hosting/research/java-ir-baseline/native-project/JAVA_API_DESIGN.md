# Java project API proposal

Design only. No public API or new implementation is introduced by this document.
The production references below were inspected at Ansatz `662ac21`; research
acceptance is separate. The integrated project-path prototype has actually loaded
the cached official-frontend tutorial artifact, prepared canonical Headers and
executed main with native-equivalent output. That proves a vertical slice, not a
general project API.

## The ordinary Java experience

Proposed shape, with deliberately unreleased names:

```java
try (Lean lean = Lean.open();
     LeanProject project = lean.loadProject(Path.of("my-lean-project"))) {
    MainResult result = project.runMain();
    System.out.print(result.stdout());
}
```

Configure a nonstandard official toolchain/cache location once through the Lean
builder when needed. Ordinary calls do not mention exporter commands, Python,
IR, Clojure CLI, provider registries, ModuleData, codecs or certificates.

`loadProject` owns source capture, project discovery, native frontend compilation
when needed, cache validation and immutable code preparation. `runMain` runs the
loaded project; it does not silently invoke a native executable as a fallback.
Compile diagnostics are returned as stable structured diagnostics before any
Java execution. Unsupported project/runtime capabilities fail explicitly.
Diagnostic severity/positions come from the actual frontend message log/file
map when available; retain raw diagnostics otherwise rather than inventing spans
or categories from exception-message text.

Provide two deployment paths, with names still subject to API discussion:
`loadProject(path)` owns native source compilation/cache for development, while
`loadArtifact(resource)` loads a previously built bounded compiled artifact using
only the JVM. A Maven/Gradle build plugin can compile `src/main/lean` with the
configured official compiler and packaged helper, then put IR, typed entry
evidence and provenance in the application JAR. Production applications need
only ordinary runtime dependencies: no Lean installation, Python, compiler or
manual export step. Current artifact preparation already demonstrates loading
without invoking Lean in the JVM process. The native checker remains a build-time
trust boundary; artifact loading still validates bytes, format, target, exact ABI
and runtime capabilities. A compiled artifact is not a JavaTC proof certificate.
This reduces deployment friction independently of the hosted frontend roadmap.

For a separately implemented typed-function gate:

```java
LeanFunction<BigInteger, BigInteger> step = project.function(
    "Example.step", LeanTypes.function(LeanTypes.NAT, LeanTypes.NAT));
BigInteger answer = step.apply(BigInteger.valueOf(40));
```

The type descriptor requests a checked match and chooses immutable Java value
conversion. It is not caller proof of the function's Lean type. Initially support
closed monomorphic unary Nat/String functions; do not imply polymorphism,
dependent arguments, arbitrary IO values or arbitrary Java object binding.
BigInteger preserves the complete admitted Nat domain, including beyond long.
Strings preserve Unicode/NUL exactly. Raw Node/Expr/CI aliases never become
ordinary Java values. `runMain` is the simple dedicated IO Unit operation.

The existing `ansatz.kernel.Name` remains the structured identity type for expert
overloads. Dotted String convenience uses string segments, never parses numeric
segments or authorizes identity by display text. Generated private names are
resolved internally from actual compiler metadata.

## Project state and lifetime

One loaded Project owns one shared persistent project world and one serialized
runtime branch. Repeated function calls reuse code, checked symbol/type evidence,
runtime globals and caches. Do not create a new classloader, reload source or
restart the JVM on every call. The current tiny runner's fresh engine per call is
a test implementation, not this proposed project-state contract.

Internally distinguish immutable ProjectVersion (captured source DAG, native
compile evidence, canonical Program/Headers, symbol/type index, optional kernel
Env overlay) from the branch's mutable execution state. Handles bind the exact
version, Project lease and entry Header. A later reload creates an explicit new
version; an old handle cannot quietly target a different body. Fork is later:
Java kernel Env persistence alone does not fork runtime globals, source regions,
active checked associations or pending host requests correctly.

Project.close serializes with calls, releases known result/cache/stream owners
while required services remain active, closes its resources and invalidates its
handles. Lean.close closes retained child projects and then shared code/store/
toolchain resources. Ordinary users own these two AutoCloseable scopes, not every
internal immutable context returned by a helper. Close is idempotent. No Cleaner
is a substitute for known-owner disposal.

On a runtime failure, preserve exact internal custody, prevent replay/continued
use of the failed branch and produce a bounded LeanExecutionException with its
cause and diagnostics. A normal close or a safe engine-abandonment policy must
be validated for the admitted v1 value/IO profile before release. It must not
pretend unknown callback/finalizer stages were discharged. Expired host-idle
budgets are rebased before retirement effects; argument rejection is pre-effect.

Generic execution must use explicit/resumable Engine start/advance/take with
cooperative instruction/work, deadline and output limits plus cancellation at
host-controlled quanta. The accepted fixed six-row synchronous `j.call` is not
the general implementation: total Lean functions can take impractical time and
partial IO programs can loop indefinitely. Cancellation must remain available
without launching another JVM or restarting a frontend.

Before generic release, establish a restricted pure-JVM-value/captured-stdio
abandonment policy for budget/failure boundaries. After advance returns, an
admitted branch with no external handles/tasks/callback resources may have a
separately reviewed host-reference abandonment path. That must be reported as
abandonment, not normal guest RC/finalizer discharge. Active frames cannot simply
be passed to close and called disposed. Profiles with external resources require
their actual owner-aware teardown or retained quarantine. Captured output may be
partial; neither cancellation nor close rolls back IO or retries an entry.
The failed/cancelled runtime branch becomes unusable while immutable code and
independent persistent kernel metadata can remain available. Public defaults can
be simple; these lifecycle guarantees must exist underneath them.

## Existing facade: preserve it, do not mislabel its backend

Production already has `modules/lean/src-java/ansatz/lean/LeanRuntime.java` and
`modules/lean/src/ansatz/lean.clj`. Its provider-first `PreparedProvider`,
`LeanContext`, SourceRequest, CallSignature and persistent-child lifecycle are
real APIs. Their implementation delegates to the older resident World backend.
It is not the new Java IR runtime, and its checked-provider requirement must not
be bypassed by returning a map containing the new tutorial artifact.

Keep that surface compatible. Add a project-oriented entry point separately,
for example `ansatz.lean.Lean`, backed by a separate Clojure namespace and Java IR
service. This avoids the existing LeanRuntime static initializer eagerly loading
the resident backend for the new route. Reuse Name conventions, immutable Java
DTO handling and exception design where their contracts match. Do not route new
Java IR calls through old World codecs without an actual carrier adapter.

The existing optional module's POM pins Pattern for its older compiler feature.
The new interpreter route does not need that compiler. Prefer a small optional
artifact (proposed `org.replikativ/ansatz-lean-jvm`) or an explicit module split
rather than requiring both backends and Pattern for a simple project loader.
The coordinate/name is a packaging proposal, not an announced release.

## Native frontend and initialization boundary

First mode uses the official pinned native checker/compiler as a configured
installation dependency. The loader owns ProcessBuilder/cache orchestration in
JVM code. It runs the original compiler/helper, retains actual roles, ordered
initialization plans, imports, dependency closure and entry-type evidence, then
executes original IR in Java. Version/cohort incompatibility fails before entry
execution. There is no silent switch to native execution after IO begins.

The present prototype is intentionally fixed to three exact FP Lean source
hashes and six exact IR rows. It must not be marketed as general loadProject by
removing those checks. A minimally useful v1 must accept a bounded ordinary local
project whose supported source/IR/IO is determined by actual compilation, with
an honest explicit unsupported frontier. Start with local sources and data-only
Lake configuration, ordinary Init imports, no external package resolution or
arbitrary user build-script evaluation. Use original native header parsing and
module discovery, not a Lean syntax recognizer or filename-based import proof.

For each module, export all local metadata needed for later named handles,
authentic selected static IR closures and actual initialization plans. Preserve
closed/ground/value/initialized roles. Execute admitted required initialization
in source/module order or reject it before program execution; do not infer empty
initialization from body shape. The current entry-closure tutorial has genuine
empty local plans, but does not prove all imported Init initializer parity.

Runtime capability checks concern actual native symbols/ABIs and selected
execution paths. Initially support captured stdout and admitted pure functions;
filesystem/network/asynchronous/callback profiles are separate. Static closure
completeness is not arbitrary dynamic AP completeness. Unsupported dynamic
boundaries must remain stopped rather than receiving fake success values.

The hosted frontend destination can implement the same internal ProjectVersion
interface later, after actual default Init extension/initializer and matching
kernel association gates. That backend choice is implementation/configuration,
not a matrix every Java caller must understand. Diagnostic build information
must still state which checker/compiler actually established the source facts.

## Checked type evidence for generic handles

The current fixed tutorial's explicit `main : IO Unit` source annotation was
checked by the pinned official frontend. Its `void -> object` ABI and runtime
IO.ok shape alone do not establish that source type. General handles need a new
producer export from the actual post-compilation Environment:

1. Exact typed constant Name, declaration kind, universe parameters and original
   ConstantInfo type Expr, bound to the captured module/source/compiled artifact.
2. A bounded native checked equality/instantiation result for supported requested
   signatures, or equivalent full typed evidence checked against the actual
   matching Java kernel view. A caller's TypeDescriptor is never that result.
3. Exact compiled callable/boxed bridge mapping, erased/implicit argument plan,
   original ABI/borrow flags and result codec; zero truncation or inferred boxed
   naming. Bind all of it to the canonical prepared Header and ProjectVersion.

First admit exact closed Nat/String signatures and IO Unit main. Refuse open
universe/metavariable/dependent signatures until separately implemented. Looking
up an unused function may extend the immutable Program through authenticated
additional root exports on the same compiler world; it cannot treat a random
inherited Header or displayed name as selected project code. No generic typed
function factory should ship before this evidence gate exists.

## Kernel stores: reuse the existing implementation

Proof/kernel libraries are related but independent from executing an externally
compiled entry. Do not load or recheck all Init/Mathlib before greeting main.
Do not build a second kernel database. Production already provides:

| Existing source/API | Reuse |
| --- | --- |
| `src/ansatz/store.clj`: resolve-existing, check-format!, check-compatible! | Store discovery and exact format/branch/cohort requirements |
| `src/ansatz/store/fetch.clj`: fetch!/ensure-store! | Existing named stores, checksum-checked parts, atomic installation, offline policy |
| `src/ansatz/export/storage.clj`: open-store, branch-loader, load-env | Captured PSS roots and lazy per-name CI/Expr loading |
| Same namespace: full-ci-evidence/full-ci-evidence-partition | Bounded full-CI evidence for requested Names; no eager proof hydration |
| `src-java/ansatz/kernel/Env.java` | Persistent local overlay, sameExternalView, external lookup/cache, cheap Env fork |
| `TypeChecker.java`: inferType/check/isDefEq/checkConstant/checkMutualDefinitions | Existing Java checking of requested expressions/new declarations |

A future `lean.kernel().openStore("mathlib")` can wrap that loader and lease
without invoking the process-global `ansatz.core/init!` state. A per-project or
per-thread resolver preserves current storage cache/thread assumptions; shared
immutable PSS roots are not permission to share every mutable resolver cache.
Store-backed environments already load prepared declarations on demand without
rechecking every proof at startup. Full re-verification is explicit, not default.

Keep readable schema, distribution trust, recorded verification and actual
frontend association distinct. Existing prepared stores may be used by the
independent Java kernel API now. They do not become matching guest ModuleData,
macro extensions, IR or initialized globals by loading their PSS roots. A matching
source/kernel association uses the existing exact CI/raw-payload/store guards,
not a serialized verified flag or matching version string. In particular current
legacy bundled 4.29 metadata is not a 4.33 frontend compatibility witness.

This lets Java consumers use Init/Mathlib kernel data without paying full store
replay, while hosted default Init/mapped graph/Mathlib frontend import remains a
separate implementation project. Availability of a named download follows the
actual published store index; do not promise a new full Init download merely
because local store loading exists.

## Packaging without extra user tooling

Use Maven/Gradle with Clojars and ordinary transitive JAR dependencies. Consumers
need no installed Clojure CLI, Leiningen, Python or manual exporter step. Clojure
is an implementation runtime dependency inside the JVM; Java callers see Java
interfaces/DTOs. Keep core Ansatz independent of optional execution backends.

Reuse `build.clj` and `modules/lean/build.clj` lessons: compile real Java classes
into the artifact, use an explicit source/resource closure, pin the core Maven
version in the POM, never publish development local paths, and test jars with
repository sources absent. Core's Java11 target/AOT policy remains unchanged.
Target JDK17 initially for the optional runtime, consistent with the existing
optional facade baseline; do not infer a lower runtime baseline from DTO bytecode.
Source-loaded internal Clojure is acceptable without a CLI. AOT only after the
jar-only tests establish correct classloader/protocol behavior. Runtime javac and
per-evaluation URLClassLoader creation are development mechanisms, not packaging.

The accepted prototype exporter is a large native helper. For release, bundle
or automatically resolve an independently pinned compatible platform helper and
extract it into a verified private cache. Bundle Export.lean and provenance as
well. User-built exporters are not an installation step. The attempted source
helper `lean --run Export.lean` exceeded the current 900MiB bound without output;
it is not an accepted fallback. Validate platform/ABI/sysroot compatibility and
offline packaging in an isolated consumer with no checkout paths.

Initially the official native toolchain is configured once or discovered through
documented installation conventions. It is an explicit trusted immutable input,
like the JDK or build dependencies. Cache keys bind source DAG, helper/compiler
identity/options, target and toolchain installation descriptor; hits validate
actual artifact bytes and invalidate changed installations. A reported githash
does not attest every sysroot library byte. No repeated compilation on calls and
no silent cross-installation cache reuse. Precompiled verified artifact loading
can later avoid source compilation entirely without changing the project model.
Keep portable compiled-IR cache data separate from class-bound prepared Program/
Header objects: reuse the former only through current schema/ABI admission and
key the latter by the actual runtime class/cohort. Never persist an active engine
or reuse Header objects from another classloader/runtime binary.

## Smallest coherent release gates

1. JVM-owned native build/cache path, bundled helper and ordinary Java-only
   Maven/Gradle consumer; Python remains a prototype until replaced. Also an
   artifact/resource-only runtime consumer with no toolchain/compiler installed.
2. General bounded local project discovery/export beyond the pinned greeting,
   exact initializer/capability refusal and actual entry CI type evidence.
3. One reusable Project runtime/world, runMain, at least unary Nat/String typed
   handles, repeated-call behavior, exact immutable value conversion and normal
   close/failure tests. Explicit budget/cancellation and the restricted value/
   captured-stdio abandonment gate are required; no arbitrary unsafe type bridge.
4. Jar-only API consumption plus actual greeting and additional independent
   projects; cold/cache-hit compilation and runtime timing reported separately.
5. Optional lazy kernel-store facade reusing current stores, with no default
   full Init/Mathlib replay and no implied guest-frontend matching association.

Later: runtime/source-world forks, hot reload, arbitrary Lake dependencies,
broader IO/callbacks, dependent/polymorphic handles, matching hosted default
Init/Mathlib and full JVM frontend bootstrap. These are not prerequisites for
an honestly scoped native-frontend Java runtime release, and are not implemented
by this API proposal.
