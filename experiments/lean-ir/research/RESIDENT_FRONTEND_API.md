# Experimental resident Ansatz frontend facade

`prototype.resident-frontend` now implements the explicit context facade over
`hosted-file`, `frontend`, `raw-interop`, and the value codecs. It is experimental,
not a published `ansatz.lean` API. Boundary tests use clearly labeled helper
models and captured emitted IR; actual full-Init acceptance through this new
facade remains a separate gate. The previous resident REPL port was unreachable
on October 18; no successful replacement/bootstrap is implied here.

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
distinguishes passing model/source/JAR checks from actual facade acceptance.
`scripts/resident-prelude-probe.clj` now provides the latter probe over explicit
prepared artifacts. Its 2 GiB attempt exhausted the archive-restoration heap before
frontend execution; the larger attempt was deferred by the memory preflight.
This does not extend the earlier lower-level ordinary-file observations to the facade.
