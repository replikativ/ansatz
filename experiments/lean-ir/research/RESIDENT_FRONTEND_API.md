# Experimental resident Ansatz frontend facade

`prototype.resident-frontend` now implements the explicit context facade over
`hosted-file`, `frontend`, `raw-interop`, and the value codecs. It is experimental,
not a published `ansatz.lean` API. Boundary tests use clearly labeled helper
models and captured emitted IR; actual full-Init acceptance through this new
facade remains a separate gate.

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

The experiment already compiles an ordinary implicit-Init source file and calls
Clojure from the emitted guest code. It also roundtrips a genuinely owned heap
String Ref through the already compiled function in independent forks with
isolated releases. These observations do not provide a one-command bootstrap,
general package loader, native FFI, automatic IO rollback or arbitrary Lean-file
compatibility.

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

Raw handlers remain responsible for their owned arguments/results, as in the
successful identity capability. A later typed host-handler adapter may decode
borrowed views and encode returned host values, but it needs a separate policy
for consuming owned arguments, transferring existing guest values and callback
failure checkpoints. Do not silently release a transferred result as an input,
or treat a borrowed Ref as a new owner. Reuse the actual raw callback scope for
guest reentry; no global current-world variable or escaping synchronous callback.

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
