# Experimental resident Ansatz frontend facade

`prototype.resident-frontend` now implements the explicit context facade over
`hosted-file`, `frontend`, `raw-interop`, and the value codecs. It is experimental,
not a published `ansatz.lean` API. Boundary tests use clearly labeled helper
models and captured emitted IR. The separate
[fresh full-Init acceptance](../measurements/full-init-strict-resident-acceptance.json)
now passes through `resident-preparation/open-checked`: ordinary Nat42, macro
Nat/Unicode, isolated diagnostics and two explicit host callbacks. Its 65,994-CI
strict receipt records 15 admitted assumptions. Source-module publication/import
is a separate capability: fresh Init+A strict checking passes, and the
[typed FILE witness campaign](../measurements/source-file-typed-witness-validation.json)
now passes B compilation, Nat/Unicode calls and its actual imported-origin witness.
No public packaging or general package support is
inferred from these profiles.

The optional [`prototype.resident-source` consumer](RESIDENT_SOURCE_PUBLICATION.md)
adds immediate source publication through public resident APIs, without changing
this facade or the captured runtime. Its separate
[validation receipt](../measurements/resident-source-publication-validation.json)
records focused branch/ownership/failure tests and the full prototype suite.
Its separate actual standalone acceptance also passes: publish A, genuinely
finalize/check the import, load/call B and retain A's earlier Context. Full-Init
publication through this consumer remains separate. The optional
[`prototype.resident-import` consumer](RESIDENT_IMPORT_PREPARATION.md) now prepares
one standalone published import, returning a fresh checked Context and the exact
captured request for `load-source`. The actual two-consumer frontend workflow
passes separately; over-Init preparation and general dependency graphs remain open.

The [archived prelude acceptance](../measurements/resident-preparation-progress.json)
now passes the real facade: Nat/Unicode calls, a second source, expected command
diagnostics, and two host callbacks. It restores the full authenticated runtime
bootstrap, then prepares a prelude-only Environment with exactly three checked
compiler markers. It uses explicit immutable-text sharing and guest cancellation
helpers. The 47.2-second observation includes fresh preparation and source checks,
excluding archive restore and earlier failed attempts. It is not ordinary-Init
acceptance or a throughput benchmark. The REPL was closed before rebuilding the
separately discovered kernel safety fix; the measurement records the loaded class
hashes, so it does not imply acceptance under that later checker.

The earlier low-level `hosted-file` campaign recorded ordinary implicit-Init
compilation, source-macro execution after reviewed recovery, and Lean–Clojure
Nat/Unicode calls ([ordinary](../measurements/hosted-ordinary-answer.json),
[macro](../measurements/hosted-ordinary-macro.json),
[interop](../measurements/hosted-ordinary-interop.json)). Those 2026-10-17
observations used a long-lived, resumed Init world and its then-loaded checker;
they predate the later definition-safety fix. They do not establish ordinary-Init
acceptance through this facade or `resident-preparation/open-checked`. Fresh
safety-validated resident evidence covers the standalone KernelImportProbe
profile, including [separate-process checkpoint restoration](KERNEL_PROBE_GENUINE_SOURCE.md)
and the [checked preparation adapter](../measurements/checked-resident-provider-acceptance.json).
Ordinary Init through that adapter and fresh bounded full-Init reproduction were
open at that stage; the subsequent full-profile receipt above establishes them.
Reusable import preparation, ordinary full-Init dependency edits and public
packaging remain separate gates. A separate
[prelude campaign](../measurements/prelude-semantic-forks.json) passes actual
semantic dependency edits and retained old-fork calls through a shared JVM output
cache; that orchestration has not yet been integrated into this facade.
An earlier already-compiled-code test also roundtripped a genuinely owned heap
String Ref through independent forks with isolated releases. None of these
observations provides a one-command bootstrap, general package loader, native
FFI, automatic IO rollback or arbitrary Lean-file compatibility.

## Small first API

The prototype namespace is `prototype.resident-frontend`. A public `ansatz.lean`
namespace still requires a packaging decision. The implemented operations are:

```clojure
(def context
  (resident/adopt-prepared prepared
    {:trusted-functions trusted-preparation-functions
     :trusted-bindings trusted-preparation-bindings
     :application-extern-symbols #{"ansatz_host_identity"}}))

(def loaded
  (resident/load-source context
    {:path "Answer.lean"
     :module-name (Name/fromString "Answer")
     :roots [(Name/fromString "ordinaryAnswer")]
     :initialization :run}))

(def called
  (resident/call (:context loaded) (:file loaded)
    (Name/fromString "ordinaryAnswer") []
    {:arguments [] :result :nat}))

(:value called) ; 42 for this concrete fixture
(:context called) ; matching world/session and owned active Environment/Options
```

`adopt-prepared` takes the actual prepared session/world/catalogue/Environment/
Options, not a native Environment pointer or a module name that silently triggers
import. It requires an existing checked kernel association and pinned producer/profile
checks. Independently retained `:trusted-functions` and `:trusted-bindings` are
explicit host preparation capabilities; checking a candidate map against itself
would not establish code provenance. Missing producer commit metadata remains
missing, not inferred. Existing live kernel authority comes only from the actual
association, never a serialized boolean. Adoption rejects suspended/active worlds
and validates session/world function-map identity. Bootstrap preparation, runtime capabilities,
Init completion and import preparation remain separate explicit operations.

### Opening an actually checked Environment

`prototype.resident-preparation/open-checked` is the common adapter when strict
import checking has returned an owned guest Environment but the caller has not
acquired an Options owner yet:

```clojure
(def context
  (preparation/open-checked
    {:world checked-world :session checked-session :environment owned-environment}
    {:catalogue trusted-catalogue
     :trusted-functions trusted-preparation-functions
     :trusted-bindings trusted-preparation-bindings
     :kernel-helpers trusted-kernel-helpers
     :frontend-configuration frontend-configuration
     :application-extern-symbols #{"ansatz_host_identity"}}))
```

The adapter validates the independent executable/binding registries, producer
manifests and selected frontend/helper closures before guest association lookup
or Options acquisition. It then uses the identity-authorized kernel helpers to
resolve the actual live checked association. Caller certificates, phase labels
and restored checkpoint flags provide no checking authority. Only after this
lookup succeeds does it retain one owner of the actual initialized
`Lean.Options.empty` global and delegate to normal resident adoption. It does not
import modules, run initialization, insert compiler markers or link missing code.

Preparation must complete the selected guest Name-encoder closure before
capturing its final trusted function registry and bindings. Resident adoption now
protects this host-invoked closure alongside the compiler, header, witness and
kernel helpers. `:encoder-options :helper` selects the guest helper; explicitly
supplied custom host encoder callbacks remain trusted host code whose arbitrary
dependencies cannot be inferred. The older source97 checkpoint profile retains
its original 312,167-function registry and explicit additive-encoder compatibility
step; it is not silently upgraded to a new preparation/build profile.

Failure data keeps separately named `:resident-preparation-entry`,
`:resident-preparation-associated-entry` and, after acquisition,
`:resident-preparation-options-entry` packets. Adoption additionally preserves
`:resident-adoption-entry`; `:checkpoint`/`:checkpoint-session` identify the newest
helper checkpoint where available. These are alternative immutable branches,
not extra owners in a later world. Inspect their exact ownership before cleanup;
do not combine an earlier Options root with a different failure checkpoint or
retry a guest operation because an old branch remains available.

The returned Context owns Environment/Options in its branch. The startup caller
continues to own the native source or checkpoint ResourceLease. Closing a Context
or fork leaves that shared resource open; close every borrowing Context and
discard diagnostic worlds before closing the shared lease. This adapter does not
turn checkpoint publication into a checked kernel receipt or general file loader.

The [genuine adapter run](../measurements/checked-resident-provider-acceptance.json)
used fresh authenticated preparation with the Name encoder included before final
binding capture. After actual guest finalization, native/guest checking of all
17 declarations and the same-environment marker extension/check of 20 declarations,
`open-checked` returned a Context. It compiled the matching-header source, returned
Nat42 and exact Unicode, made exactly two Lean-to-Clojure callbacks and produced
one expected diagnostic without an executable handle. All Contexts and alternative
worlds were closed/discarded before closing the external source. The process exited
0 under a 2GiB heap; its 335.72-second lifecycle includes preparation and interactive
idle, not isolated provider or compilation timing. This new preparation is distinct
from the old source97 checkpoint profile; it used no additive encoder repair or
checkpoint reinterpretation.

Final validation passed 782 experimental tests / 66,289 assertions and 822 library
tests / 3,591 assertions. The library run used an isolated store root and loopback
fixture servers, with optional Mathlib integration excluded. Earlier attempts hit
the sandbox's durable-store/socket restrictions and a 512MiB corpus-test heap limit;
the final isolated, loopback-enabled 1536MiB-heap run passed. The measurement pins
the tested sources, harnesses and guard outcomes.

### Next startup compatibility boundary

The current checkpoint recipe conservatively pins the whole host source tree.
That makes an unrelated resident-tool or benchmark edit invalidate a checkpoint.
A proposed **new** profile can separate these identities:

| Layer | Required identity |
| --- | --- |
| Guest image | Checkpoint bytes, Lean/runtime profile, source descriptors, catalogue/overlays and exact prepared code |
| Execution and restore authority | Reviewed core source closure, actual loaded kernel classes, dependencies, factory and checking policy |
| Host tooling | Separately approved frontend/resident/application code declaring its supported core profile |

This is a planned compatibility improvement, not an implemented migration. Keep
core byte identity initially; an ABI label alone is insufficient. Audit both static
and dynamic dependencies, generated code, resources, classpath shadowing and `.cljc`
branches. `interop-codec` and `guest-encoding` remain core dependencies today because
evalConst and kernel capability implementations call them. The resident/frontend
facades appear separable, subject to that complete dependency audit. This boundary
does not sandbox arbitrary trusted Clojure host code.

The existing source97 contract must remain unchanged. A new profile needs a new
capture and launcher receipt for both core and host-tool identities, fresh checking
after restore, rejection tests for core/checker/codec/factory/resource changes and
an actual restore-to-source repetition. Core namespaces must stay loaded without
reload/redefinition. Separately versioned tooling should improve REPL iteration
without recapturing guest state for unrelated host edits.

### Loading and calling source

`load-source` accepts the existing exactly-one-of `:path` or `:text` plus file name
contract and real kernel Names. It delegates to `hosted-file/run-file` without
calls, keeps initialization explicit, and returns updated context, actual command
diagnostics and an admitted file handle on success. Keep module names/roots
explicit; do not infer them from paths, guessed dotted identifiers or host type
reflection. No native per-input compiler is involved.

A failed compilation returns the actual partial Environment/session/checkpoint
for inspection, no successful file handle and no final bundle installation.
Earlier successful commands or macro IO may already have occurred. The old
immutable context is a diagnostic fork, not permission to retry effects. Do not
silently replace the partial Environment with the previous or empty one.

`call` uses only a file's admitted boxed-entrypoint mapping and exact current
unit identity. It validates actual admitted IR parameter/return types, ownership,
and initializer completion before encoding. It uses boxed value codecs and invokes `raw-interop/call` in the current
world. It must preserve the actual session returned by execution because a host
callback can link more code. Decode borrows; an ordinary decoded-value mode
releases the returned guest owner exactly once and clears the world result alias.
An optional raw-result mode must return an explicit owned handle with documented
release responsibility. Do not release an IO error's borrowed payload while
reporting it; preserve the completed result owner/checkpoint on decode failure.

Keep `call-io` explicit: append the actual erased world token only under an
explicit IO contract and decode `[:io result]`. Object return type does not imply
IO. Polymorphic erased arguments use the new explicit `:erased` descriptor
with nil host input. Actual void/erased ABI parameters require it; object parameters
may also carry an explicit erased argument. Boxed scalar adapters box/unbox
UInt64/Float values explicitly; no type parameters are inferred from object IR.

## Context and ownership lifecycle

A context owns its active guest Environment and Options, alongside its matching
world/session and trusted catalogue. Loading returns another owned Environment.
When replacing the active Environment in the returned branch, release the old
context's owner in THAT branch exactly once; preserve the original context's
independent immutable world. Options stay owned across loads. Treat an identical
old/new Environment Ref carefully: the returned helper owner and borrowed input
owner are still distinct logical owners.

A file handle should hold unit digest, module and admitted entrypoint mapping,
not a raw callable detached from its checking/code authority. Validate it against
the current world's unit registry before use. Cross-context numeric Ref IDs are
not capabilities; reject handles from incompatible worlds or changed units.

`fork` creates a separate close token over the immutable guest snapshot. It branches an immutable snapshot and shares immutable artifact storage and
semantically keyed code cache; it does not create an independent OS entropy
stream or replay arbitrary external IO safely. Runtime session/program caches
can be mutable optimization state without becoming shared guest state. Preserve
backend, fuel, compile threshold and the exact shared cache when reopening a
session. Never solve lifecycle problems by rebuilding full Init for each file.

`close!` consumes the context's one Environment and one Options owner once;
contexts also implement `java.io.Closeable`. It does not close shared ModuleData
stores or invalidate descendants. Artifact-store lifetime remains external.
`initialize` executes only an admitted unit's initializer plan without recompiling
source; current guest guards/evidence prevent replay of entered failures.
Borrowed call arguments remain facade-owned until successful decode; failures
name them separately from the owned returned result or alternate frontend packet.

## Explicit host bindings

`with-externs context bindings` adds application raw bindings without replacing
any existing runtime or application handler capability. New application symbols
must be in the independent preparation's `:application-extern-symbols` allowlist;
known runtime symbols, the `lean_` namespace, and catalogue exports remain reserved,
including when their implementation has not yet been linked. Require exact IR parameter/return types and borrow flags, and reopen
only the matching session while preserving the function map and execution options.
A newly compiled source extern is admitted through the existing lowerer's ABI
checks. Do not infer a signature from a Clojure function or reinterpret an unknown
extern as a host call. Protect bootstrap/kernel/import/compiler capabilities from
incidental replacement; distinguish application extern configuration explicitly.

Raw handlers remain responsible for their owned arguments/results. The optional
[Nat/String typed adapter](TYPED_EXTERNS.md) accepts explicit ABI, codec and
ownership descriptors. It decodes borrowed semantic values, independently encodes
the host result, then consumes each owned input occurrence once. Borrowed
positions cause no decrement; an owned alias may release the same header after
decoding. It preserves actual raw callback scope and terminal failure ownership
packets. Existing guest Ref transfer, IO, bytes and closures need separate
contracts; they are not inferred or accepted by this adapter. Guest reentry still
uses the actual raw callback scope, without an escaping synchronous callback.

`prototype.interop/call` has useful codec code but a different session model:
it starts calls from `:initial-world` and its existing host lowering is narrower.
Do not route the resident frontend through it wholesale or lose current macro
code, kernel associations, module receipts or session/cache updates. Build the
thin facade on the raw/hosted path already exercised by ordinary files.

## Import and packaging boundary

Initially accept only source headers matching the explicitly prepared Environment.
`compileImportedFileState` checks exact requested imports and module mode.
Pinned Lean 4.33.1 prepends BOTH ordinary Init and meta Init to an ordinary file:
A's header is `[Init, meta Init]`, and an ordinary `import A` file requests
`[Init, meta Init, A]`. Both implicit Init records have `importAll=false` and
`isExported=true`, differing in `isMeta=false` versus `true`. Preserve their
order/flags even when the effective module closure merges the same module name;
`needsIRTrans=true` is legitimate for this exact ordinary prefix. A
caller cannot ask the facade to satisfy `import A` by editing that header or
retaining A's local compilation Environment. The ordinary Init-plus-owned-source
hybrid import profile remains a separate implementation; see
[HOSTED_SOURCE_MODULES.md](HOSTED_SOURCE_MODULES.md).

A later explicit bootstrap constructor can validate pinned helper artifacts,
producer catalogue, ModuleData source hashes, runtime profile/capabilities and
kernel policies, then build/adopt a prepared context once. Existing
`bootstrap/load-file!` performs native per-input elaboration; it must not become
the hidden implementation of a supposedly hosted `load-source`. Avoid claiming
that the current bootstrap-only archive already persists all live imported
kernel associations, source receipts and resident context resources.

## Acceptance gates

- Reject mismatched function maps, absent checked Environment/Options, incompatible
  producer profile, stale handles and protected binding replacement before any
  guest effects or argument transfer.
- Exercise modeled orchestration plus captured emitted IR and real guest Name
  encoding for load→call→second load, shared-cache retention and independently
  forked contexts. Check unit/code identity, initialization completion and exact
  fuel/pause behavior through existing lower layers.
- Verify explicit Nat, Unicode String, bytes and IO codecs; raw heap Ref roundtrip;
  one-time result release; identical Environment Ref owner replacement; and closure
  capture/owned argument lifetime. Do not duplicate lower-layer arithmetic tests.
- Check diagnostic compilation preserves actual partial context and unstarted
  inputs, and call/callback/decode failures preserve exact active session,
  completed results and transfer evidence without cleanup guesses or retries.
- Run a separate actual resident acceptance canary using the already prepared
  full-Init context: load a new ordinary file, bind a host extern and call it;
  include an error case. Keep its observation distinct from helper-model tests.
  Do not rebuild full Init inside every focused test or call it complete Lean
  compatibility because these cases pass.

The first implementation should package proven operations and make ownership
convenient, without redesigning import semantics, adding implicit initializer IO,
changing native representation profiles or weakening interpreter-witness checks.


The [foundation validation record](../measurements/resident-session-foundation.json)
preserves the earlier model/source/JAR checks and unsuccessful archive attempts.
The later [preparation record](../measurements/resident-preparation-progress.json)
records actual **prelude-only facade acceptance**, both in the REPL and from a
fresh JVM against the rebuilt, safety-validated kernel. The standalone probe
loads two Lean sources, calls Nat/Unicode values, preserves an expected diagnostic,
and makes exactly two Lean-to-Clojure callbacks. It checks the actual three
compiler markers before associating the kernel environment.

The fresh run used a 3 GiB heap, completed in 163.58 seconds including JVM startup
and authenticated archive restoration, and peaked at 3,276,877,824 bytes of
process-group RSS. Its explicit `:immutable-text-v1` ShareCommon profile covers
host-backed immutable strings. This is acceptance evidence, not a throughput
benchmark or ordinary/full-Init facade support. Completed full-Init checkpoints,
warm dependency edits and broader native representation profiles remain open.


The next [assembly-only probe](../scripts/full-init-assembly-probe.clj) also passed
against the current runtime and rebuilt kernel. It opened the authenticated Init
transport (631 modules, 11,233,359 backing nodes), prepared 312,102 executable
functions, and ran the guest batch assembler. Preparation plus assembly took
83,563 ms after bootstrap restoration, including diagnostic host GC. The 3 GiB
heap process peaked at 3,534,254,080 RSS bytes; its 444-second guarded lifetime
includes REPL idle and cleanup and is not an assembly throughput measurement.
The [assembly record](../measurements/full-init-assembly.json) pins inputs and
scope. Backing nodes remained lazy. The experiment released its two owned roots,
discarded worlds, and closed the borrowed source. It did not run the finalizer,
create a kernel association, or produce a durable Init checkpoint. Ordinary
facade acceptance still requires those later gates.


A [three-way assembly observation](../measurements/full-init-assembly-tiers.json)
then forked the same prepared idle world, executable map, bindings and open source.
Mutable interpretation took 4,301.82 ms; JVM demand compilation at threshold 64
took 7,725.80 ms with an empty code cache and 5,147.54 ms reusing that cache.
All three executed exactly 2,091,800 guest steps and produced identical local
heap/global changes, roots, allocation identity and initialization state. The
cold JVM branch compiled 237 blocks; the warm branch compiled none. Each branch
released its two owned roots. This fixed-order observation shares source, OS and
JVM caches; it measures assembly alone and cannot predict finalizer performance.
For this workload, demand compilation did not improve elapsed time. The
[definitions-only benchmark](../scripts/full-init-assembly-benchmark.clj) accepts
a still-open result of the assembly probe; loading either script starts no guest
work. The final input assembly was released and the source closed after all
comparison branches were discarded.


The next [typed-witness preparation](../measurements/full-init-typed-witness-preparation.json)
passed on those actual full-Init assembly inputs. Three pinned additive stages
added 24 declarations and 14 executable functions in approximately 2.64 seconds.
Every existing executable and every other capability object was preserved.
An independent comparison confirmed the entire guest world except its function
map was equal, with identical heap/global maps, unchanged owned roots and source,
and zero additional guest steps. The final evalConst binding captures the completed
catalogue and executable map. This validates preparation and identity preservation;
it does not execute the typed witness or finalize Init.

The [preparation/slice draft](../scripts/typed-witness-next.clj) and
[host-control tests](../scripts/typed-witness-control-test.clj) are definitions-only.
Load the existing typed/shared-name helper scripts first, then the preparation
draft. Five host-control tests passed 43 assertions with a stubbed driver: duplicate
starts/continuations do not replay work, invalid continuation preflights preserve
the token, and unwound nested host callbacks cannot resume as outer guest states.
The slice helpers are experimental, preserve live checkpoints only, and do not
provide durable restoration or nested host-continuation serialization. No finalizer
was invoked in this run. All assembly roots were released and the source closed.


A subsequent [host-control validation](../measurements/full-init-typed-witness-controls.json)
passed seven tests / 119 assertions. The current draft also checks idle state,
exact executable/source identity and live roots before opening or claiming a
start. Two callers racing on either start or continuation enter the stubbed driver
exactly once. These strengthen the captured preparation revision; the later
preflight/race tests do not execute Init finalization.


Initializer setup had a measurable retained-memory cost independent of guest
execution: it expanded and kept a separate transitive guard set for each of 6,966
native symbols. The [same-input host measurement](../measurements/initializer-guard-memory.json)
uses 2,326 actual plans extracted from the authenticated declaration index and
pinned overlay manifests, without loading the unrelated declaration map. The
shared dependency graph reduces retained binding data from approximately 414 MB
to 3.6 MB. Construction took 19.8 seconds before and 0.11 seconds after in separate
fresh JVM observations. Every reachable guard is still checked against the current
world; cycles, split phases and partially entered closures preserve the earlier
availability policy. No initializer actions or completion receipts are invented.

Checking all 6,966 symbols on complete tiny host worlds took 3.67 seconds with the
old retained sets and 9.29 seconds with query-local ArrayDeque/HashSet scratch.
This CPU/memory tradeoff is explicit: the guest world stays immutable and no
availability result is cached across snapshots. These figures do not predict full
frontend/finalizer timing or establish a smaller JVM resource ceiling. Differential,
alternating-world and concurrent-query tests cover guard and ownership behavior.
The [input extractor](../scripts/prepare-initializer-memory-inputs.py) and
[host benchmark](../scripts/initializer-memory-benchmark.clj) reproduce this scoped
experiment using the pinned artifacts. Full runtime validation is recorded with
the measurement when complete.


The [cooperative boundary validation](../measurements/cooperative-host-boundaries.json)
adds an opt-in raw API for the next finalizer experiment. `advance-to-boundary`
runs a bounded outer guest segment and yields before an unstarted host handler.
`complete-host-boundary` claims its process-local token once, completes that one
synchronous handler under a separate aggregate helper-instruction budget, and
returns immediately after resuming the outer control state. It executes no next
outer instruction. Nested helpers stay synchronous; a failed completion cannot
resume its lost host continuation. Tokens grant no durable restoration or IO
isolation across deliberately forked worlds.

The same dispatcher serves existing `raw/call`/`continue`, preserving their exact
fuel and capability behavior. Cooperative completion conservatively poisons its
helper budget on a throwing backend; catching that error cannot produce further
helper work or a success receipt. Existing ordinary calls retain their earlier
catch-and-return behavior. Fuel bounds guest instructions, while host checking,
parsing, bytecode compilation and IO still need their own resource policies.

Focused checks passed 36 tests / 749 assertions; the full runtime suite passed
742 tests / 65,901 assertions. A genuine native-compiled fixture exercised UInt32
wraparound and owned Unicode/NUL/emoji IO Strings through the new boundaries on
all three backends, with no handler before yield, no duplicate completion and
complete result cleanup. This validates compiled-fixture interop, not actual
Init witness production. The next actual REPL run combines this protocol with
the smaller initializer graph and prepared typed/shared-name witness.

The [actual cooperative run](../measurements/full-init-cooperative-run.json)
subsequently completed 793 real `evalConst` callbacks without failure on a 2 GiB
heap. It advanced 161,574,741 guest instructions from the assembled state and
ended with 323,943 functions and 534,583 local heap objects. The first typed/shared
witness callback took 2.51 seconds and 144,923 helper instructions. The scoped
diagnostic process exited normally within its 2,560 MiB RSS policy, peaking at
2,499,514,368 bytes. Guest finalization was still unfinished; no kernel checking,
resident adoption or durable completed-world checkpoint occurred.

The same run tested a short persistent-interpreter prefix before mutable
execution, using a scoped REPL replacement of the boundary runner. A pure
51-instruction helper over the same 379,342-object heap took 50–88 ms in the later
mutable samples and 0.11–0.22 ms with the prefix. These are paired helper timings,
not frontend throughput: actual initializer workloads differ, and the process
also included REPL idle time and an accidental large diagnostic print outside
the timed guest segments. No end-to-end startup comparison follows from it.

The [prefix callable](../scripts/reference-prefix-experiment.clj) and
[differential/microbenchmark helper](../scripts/reference-prefix-smoke.clj) are
definitions-only experiments. Forty-two existing tests / 1,052 assertions passed
under the scoped replacement, alongside 147 canonical-state comparisons and
21 tail/fuel comparisons. A general runtime option remains deferred: it must
preserve mutable code/register admission, define conservative canonical-snapshot
eligibility, and survive frontend/resident session rebuilding. The default
runtime has not changed.

The [campaign runner](../scripts/full-init-campaign.clj) now retains the original
catalogue, helpers, policy and session explicitly. Its independently callable
preparation, automatic finalizer and strict-check phases claim owners once and
preserve intermediate successful packets before fallible work. The
[cooperative driver](../scripts/cooperative-full-init-drive.clj) authorizes the
whole active binding registry, including nested callbacks. Both record successful
events before observation, and publish a claimable phase only after its fallible
logging completes. Failures retain named diagnostic alternatives, never an
automatic retry of a consumed token or IO result. Source lifetime remains under
the caller's control. The next actual run will stop after guest completion to
inspect available resources before starting strict checking.

[Orchestration validation](../measurements/campaign-orchestration-validation.json)
passed 22 focused tests / 183 assertions, followed by the full runtime suite of
764 tests / 66,084 assertions. The owner/publication tests use small models;
they establish failure handling, not actual full-Init or resident acceptance.
See the [REPL campaign instructions](../scripts/FULL_INIT_CAMPAIGN.md) for explicit
phase entry points and resource/lifetime requirements.

The [subsequent default-mutable run](../measurements/full-init-default-fuel-failure.json)
stopped terminally on callback 1,123 after 1,122 successful `evalConst` callbacks.
The shared-name witness for the generated UInt theorem macro exhausted its
20-million-instruction completion budget. The paused helper had 79 frames and
included `Array.append._redArg`; it did not exhaust the memory guard. Source
review found that this witness still uses the recursive dependency collector,
whose repeated suffix-array appends can take quadratic work on long IR bodies.
The authenticated catalogue body supports that diagnosis; the selected paused
guest declaration was not separately projected and compared before disposal.

The run used a 3 GiB heap, peaked at 3,551,911,936 bytes RSS, and exited cleanly
after bounded failure evidence was saved. Its 2,001.91-second process lifecycle
includes preparation and idle diagnosis and is not an import benchmark. The
failed callback was not retried. Guest finalization, strict checking and ordinary
resident acceptance remain incomplete. The next experiment combines shared-name
projection with the existing order-preserving linear dependency collector in an
additive helper, with exact parity checks before another actual campaign.

The [shared-name/linear witness validation](../measurements/shared-linear-witness-validation.json)
now establishes that additive helper's isolated behavior. All 497 previous shim
declarations remain unchanged. Native checks cover dependency order and duplicates,
four complete small witnesses, and the actual failing UInt macro: original and
new complete witnesses have identical 1,409,498-byte output covering 930
declarations, with no missing dependency or sorry evidence.

An independently verified compacted fixture carries the actual native-selected
macro body, its declaration and native dependency oracle. Guest preparation
matches body, declaration, native JSON and authenticated catalogue IR exactly.
Only 46 functions are linked, without restoring the frontend or replaying Init.
Under the same 20M instruction budget, the original collector exhausts fuel;
the linear collector completes in 154,177 instructions and returns all 1,522
dependency occurrences in the exact native order. Its result owner and all three
backing Stores are closed after the separate branches are discarded.

Twenty-six synthetic mutable-backend samples also pass: at depth 8,192, the
linear path completes in 1,573,098 instructions while the original exhausts 20M.
Wall times include shared native lookup caches and are not cold frontend timings;
native compilation has different costs and no general native speedup is claimed.
The expanded orchestration checks pass 26 tests / 295 assertions, followed by
768 runtime tests / 66,196 assertions. Full guest witness completion and the next
Init finalization remain separate acceptance gates. The campaign selects the
candidate through an explicit authenticated preparation option before capturing
the final capability; its default remains unchanged.

The canary builder, guest probe and same-stream verified-index API are now
tracked with [reproduction instructions](../scripts/ACTUAL_UINT_COLLECTOR.md).
The integrated native build passes; the probe's tracked definitions load without
starting work. Four additional index tests cover lazy blob reads, same-open-stream
authentication under path replacement, real IR execution, and malformed input.
The integrated focused run passes 30 tests / 307 assertions and the full runtime
passes 772 tests / 66,212 assertions. These checks do not advance the unfinished
Init finalizer or grant a restored kernel verdict.
