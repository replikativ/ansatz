# Explicit runtime-cohort research components

This package consolidates reviewed host definitions used with the artifact-relative
Lean frontend. It is research code, not a released backend, general project loader,
bootstrap image, or independent kernel replay of the imported Prelude. It changes
no Java runtime, kernel, Nat source profile, or historical frontend acceptance file.

The components retain their existing namespaces and opaque lifecycle. The heartbeat
Provider registry is issued once; copying a source file does not permit reloading it
under live tokens. A new actual CodeReceipt gets its own source binding, Headers,
cache policy and service callbacks. A class-binary rollover also needs a new class
basis and same-class ModuleData preparation. No source hash, manifest or descriptor
in this directory is itself an admission capability.

## Load definitions explicitly

First load the current baseline and the existing artifact-frontend package. The
prerequisites are listed in `loader.clj`; baseline definitions must include the
reviewed StdIO installer bridge. No Interpreter jar is automatically found or loaded.

```clojure
(load-file "research/java-ir-baseline/runtime-cohort/loader.clj")
(ansatz.research.ir.runtime-cohort-loader/load!)
```

`load!` preflights every file hash and rejects **any already loaded unit namespace**
before loading anything. It opens no catalogue/store, mints no receipt, constructs
no engine/image, installs no provider/default, and runs no test. It must not be used
in a retained REPL where these namespaces were already loaded from ignored files.
Use the already loaded functions there; do not use `:reload`, re-evaluate a `deftype`,
or reset an opaque registry to make the loader pass.

| File | Namespace | Responsibility |
| --- | --- | --- |
| native-init.clj | java-prelude-no-native-init | Explicit empty native-symbol policy; real interpreted fallback |
| heartbeat-counter.clj | allocation-heartbeat-counter-v1 | Pure UInt64 offset arithmetic |
| heartbeat-provider.clj | allocation-heartbeat-lab-v1 | Exact source-bound BaseIO get/set, branch state and claim journal |
| extern-bootstrap.clj | original-extern-bootstrap-v1 | Additional early original ABI descriptors, no implementations |
| limits.clj | original-runtime-limits-provider-v1 | Two original pure Unit-to-Nat queries for the pinned target |
| row-cache.clj | authenticated-raw-row-cache-v1 | Receipt-scoped bounded immutable raw-row lookup cache |
| cohort.clj | allocation-heartbeat-cohort-v1 | Explicit orchestration and consistent runtime-service routing |
| stdin.clj | original-stdin-configuration-v1 | Genuine original Buffer/Ref/Stream construction on each child |

The loader hashes detect source drift, not source or runtime trust. `sources.json`
records every copied input hash and the documented portability changes. `manifest.json`
records the complete current payload. Run the independent source audit without a VM:

```sh
python3 research/java-ir-baseline/runtime-cohort/verify-source.py
```

## Heartbeat and pure runtime queries

The heartbeat pair follows pinned Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`src/Init/System/IO.lean:594/600` and `src/runtime/io.cpp:956/961`. Both are **BaseIO**:
get returns a direct Nat, set returns direct Unit0. They do not construct `IO.ok`.
An owned Nat is an exact immutable JVM Long or BigInteger carrier; the setter's
native decrement has no JVM Node/RC effect. Subclasses/proxies and negative values
reject before effect; setter input is explicitly bounded to 4096 bits.

Each actual engine branch has its own offset: get is `(unsigned64(allocations) -
offset) mod 2^64`, set changes the offset to produce `Nat mod 2^64`. The cumulative
engine allocation field is never overwritten. Synchronous callbacks share that
branch context, even when currentTask changes. Fork captures the parent's virtual
count and calibrates the child's offset against its actual raw allocation mark.
This is logical guest allocation accounting, not native allocator, JVM heap, elapsed
time, host kernel work, or physical parity. Existing fuel/deadline limits remain.

`bootstrap-specification!` authenticates the setter metadata before its first Header.
`install!` adopts an existing canonical HOST setter or registers Header+spec when the
Name is absent. It rejects an already unavailable immutable Function rather than
pretending later registry metadata upgrades it. Actual current request, Header,
source, ABI, immutable argument and reply credits are validated before effect.
Post-effect completion failure keeps the journal and quarantines the Provider.
Keep the Provider live through callback-capable release/disposal; `revoke!` requires
an actual disposed/closed idle engine and releases only host metadata anchors.

The limits provider authenticates `Lean.maxSmallNatFn` and `Lean.closureMaxArgsFn`,
including actual target BuildIdentity, caller Header, Unit0, raw ABI and claim token.
For the accepted x86_64 target it returns Long/MAX_VALUE and 16. These are direct pure
query results, not `IO.Result`. It captures the supplied new receipt and inspects the
actual session each call; it does not retain an old engine or create source authority.

## Early descriptors and future guest exports

`data/externs` contains the reviewed 961-row metadata inventory. Its original manifest
SHA is `225d3d9e506730ffa4f6a6319ca91e6d52b46145cd6058422748b93424b5fd11`.
The complete collector checked all 375,258 index entries and 1,389,150,335 raw CAS
bytes against source index `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.
Only extern rows are retained, with original SHA pins and pretty text removed.
The portable collector takes an explicit CAS root and output directory:

```sh
python3 research/java-ir-baseline/runtime-cohort/data/externs/collect.py CAS_ROOT --output OUTPUT_DIRECTORY
```

It requires the POSIX resource-limit support used by the reviewed scan. The original
manifest records the historical collector hash and observed bounds; the adapted
collector has a new source hash and future timing/RSS/manifest bytes will differ.
Reproduction should compare index/count/row bytes, not invent equality of timings.
No collector or catalogue is automatically invoked by loading this package.

Call `original-extern-bootstrap-v1/build!` with an actual healthy parent, the explicit
inventory directory, its independently accepted manifest pin, and future guest-symbol
reservations. It reauthenticates every original row via the actual CodeReceipt and
reads actual same-class EXTERNS/current Program registries. Native and guest origin
symbols are excluded symbol-wide. Existing host ABIs are skipped exactly; other
supported overloads remain distinct. Unsupported lanes/backends and native ABI gaps
remain explicit coverage, not compatibility claims. The observed parent metadata
snapshot produced 595 additional distinct ABIs; that count depends on actual policies.

Pass descriptors through configured basis `:early-host-specifications` **before the
first captured Header registration**. The cohort appends its HB setter separately;
do not duplicate known host ABIs. An early descriptor only creates a real HostRequest
boundary. It grants no handler, success value, IO permission, compiler action or
semantics. Unknown services stop unclaimed. Later guest exports under a reserved host
symbol conflict; reserve planned origin symbols up front or reconstruct another seed.

## Explicit cohort orchestration

`open-parent!` accepts an already configured finalizer basis, new actual receipt,
explicit companion artifact directory, and trusted policy functions:

- `:open-driver! [live]` returns the actual source-bound authenticated demand driver.
- `:configure! [driver]` returns `{:driver same-driver :native-init actual-cap}` after
  the existing zero-work source policies, Substring8/Meta2 and audit21. Do not call a
  second parent importer inside this function.
- `:census!` is the existing bounded runtime-root census reader.
- Optional `:configure-child! [child journal]` constructs original stdin only after
  genuine local startup and before logical assembly/finalization/frontend work.
- `:layout-directory` is the explicit authenticated compiled-layout artifact path.
- Optional `:additional-runtime-service` is the same trusted `{:handles? fn :serve! fn}`
  map on parent/driver. Its pure classifier and handler capture the **new receipt**.
- Optional `:journal` records actual engine/source/root custody through failures.

Native-init, both heartbeat symbols, and reviewed extra queries have consistent
routing through startup, assembly, finalizer callbacks, setup's first guest call,
options proofs, checked frontend, execution and disposal. The strict wrapper keeps
actual engine/source/current-ctx/service identity, terminal/source guards and one
tick charge. Checked declaration symbols cannot be intercepted by a catch-all extra
service. Other host boundaries stop; this wrapper does not implement them.

`prepare-source-child!` takes explicit text, captured filename/module, new-class
PreparedModule, and `{:path store-path :manifest actual-manifest :layout-directory
layout-path}`. The layout path may instead come from parent policy. It is checked
before creating a child. No ignored target path is silently substituted. The stdin
callback uses original `_closed_0`, `IO.mkRef._boxed` and `IO.FS.Stream.ofBuffer`, not
a fabricated stream or an extra graph-import slot. Its construction owners are
journaled, the native default borrows/retains one credit, and the external construction
stream owner is released normally. The pristine parent stays instruction0.

Existing Module/Run/Base/declaration issuers remain responsible for source and logical
association authority. Healthy retirement transfers all owner occurrences, drives
release/disposal with the same runtime services, closes the engine, then revokes the
HB Provider and store lease. Unknown/failed/paused execution is not automatically
unwound or accepted. A thrown unknown service can quarantine its CommandRun even
though its actual request remains unclaimed; no resumable certificate API is claimed.

## Bounded raw-row cache

Create one `authenticated-raw-row-cache-v1/open-policy` per actual new receipt and
inject its resolve/check callbacks into the new driver. It calls the actual source
lease guard before access and in finally, including hits/errors. Entries hold only
recursively admitted immutable row/SHA/key/charge/LRU data; Header, Program, engine,
guest Nodes and SourceBinding are not entries. The policy intentionally retains its
receipt until close. Exact collection classes, nil metadata, string keys and immutable
scalar classes prevent hidden owner aliases, lazy realization and comparator retention.

The 256-entry/4 MiB conservative charge is an estimate, not a measured JVM heap cap.
Oversize or unsupported rows use the original lookup uncached. Typed Name keys preserve
tags/components; unsupported inputs retain original lookup behavior. Close drops row
and receipt anchors without closing caller resources. A closed/foreign lease cannot
serve cached data. The initial 16-body measurements were pressure-confounded; no
speedup claim follows from this cache.

## Verification and retained-REPL safety

`load-models!` loads definitions only, refusing model namespace replacement. Run tests
only while host/source activity is quiescent because several models temporarily
replace source callbacks. **Do not call load! in a REPL with live runtime namespaces.**
To use the frozen packaged models against already loaded identical implementations,
use `load-missing-models!`; it hashes each missing model before loading, skips existing
model namespaces, and never loads/replaces implementation namespaces. Existing model
functions remain usable; changed fixture paths should be tested in a separate fresh
source-only process, not by resetting opaque registries.

The parent executed all seven packaged model namespaces in a **separate fresh
384 MiB JVM**: 29 tests / 229 assertions, zero failures/errors, process exit 0. The
copied explicit runner loaded eight baseline prerequisite files, the existing
artifact loader, and this package/model loader. It created no engine or runtime
image and executed no guest/native program. The retained REPL also loaded just
the two missing model namespaces: 5 tests / 23 assertions passed, with zero
implementation namespace replacements. See `validation.json` for source/log hashes
and evidence attribution. These are actual packaged portability/model checks, not
only earlier ignored-source test reports.

Run the frozen runner only in a **fresh process**, with the normal source/kernel
classpath and working directory `experiments/lean-ir`:

```sh
clj -J-Xmx384m -M -i research/java-ir-baseline/runtime-cohort/check-models.clj
```

The project's ordinary development dependencies/compiled Java kernel must already
be available. `check-models.clj` deliberately calls `System/exit`; **never load it
into the retained runtime REPL**. Neither loader loads that script automatically.
The runner invokes model deftests only, not the optional actual-source `smoke!`.

Earlier component results remain useful but separate: the parent reported the
ignored-source heartbeat's authentic get/set/fork smoke (24 assertions, four tiny
engines and normal disposal), actual pure-limit requests, and real early-descriptor
metadata preparation. Those do not become new full-runtime acceptance for this
tracked consolidation. The worker launched no JVM or native process.

Historical artifact-frontend acceptance remains untouched. Parent reported the ignored
cohort components preparing actual 534-root parents and fresh Prelude-backed arithmetic
files in 384 MiB with strict publication, original compilation/IR execution, EOF and
normal cleanup. The arithmetic profile owns its separate acceptance record. This
source consolidation has no worker JVM/native run; its parent-executed definition
and model portability checks are recorded above, without new end-to-end acceptance. Source hashes identify code; they do not
mint receipts.


### General checked child construction

`prepare-general-source-child!` is an additive fresh-child entry point. It uses
`artifact-declaration-driver-v4/open-general-driver` during initial construction,
before the runtime closure is wrapped, selecting the explicit512-admission
adapter. Existing `prepare-source-child!` still selects the sixteen-admission
profile. Both use the same startup, Module/Run/Base custody, heartbeat provider
and additional-service wrappers. Command/parser/runtime/checker budgets are
separate; this selection grants no new declaration kind or import capability.
The constructor-selection models are source additions pending coordinated JVM
execution; earlier runtime acceptance records keep their original scope.

## Supported-build query routing

The five original Lean version getters use the source-authenticated pure
`original-build-identity-provider-v1` handler. It checks the actual engine's
immutable supported BuildIdentity, exact original Header/ABI and Unit before
replying. It returns direct pure values. It neither wraps IO results nor
substitutes a caller-provided version Boolean. Routing carries the actual new
CodeReceipt and rejects foreign branches even when no additional runtime service
is installed. Parent-coordinated tiny-engine tests passed 3 tests / 52 assertions;
the actual source-module export subsequently passed on a genuine Source4 request.

The pure router suite now has seven families and passed 56 assertions in the
parent's retained JVM. `load-runtime-models!` defines the separate actual-engine
version tests; invoke their `check!` with the explicitly accepted basis. They
are excluded from the pure packaged runner. No worker JVM was launched.

Parent and fresh child drivers carry their actual CodeReceipt before native
or frontend wrapper capture. Finalizer options pass the parent's exact additional
overlay contract explicitly; the legacy default remains an empty vector.
Bootstrap-specific importer and child-observer callbacks are a separate unit.
