# Artifact-relative frontend research definitions

This package preserves the stable lower units from the retained REPL experiment
as tracked sources. It is a research package, not a standalone boot command or a
shipped project-loading API. Existing namespaces and opaque token registries are
preserved. `migration.json` records the reviewed source hashes and intentional
mechanical differences; generated artifacts and runtime receipts stay external.

The package contains the original finalizer lineage controller, byte-authenticated
Prelude ModuleData capability, guarded lazy Java base, artifact declaration
request authority, v4 strict declaration adapter and driver, borrowed IR node
decoder, sequential frontend probe, option proof, and focused models. The changing
generated-IR controller and filesystem provider are deliberately separate work.

## Explicit load order

From `experiments/lean-ir`, first load the existing Java baseline and its catalogue,
kernel projection, source setup, composite-source-v4 and ModuleData graph helpers
using the parent research directory's explicit load convention. The prototype
Clojure sources and matching compiled Java classes must already be on the REPL
classpath. Then:

```clojure
(load-file "research/java-ir-baseline/artifact-frontend/loader.clj")
(ansatz.research.ir.artifact-frontend-loader/load!)
```

Loading defines functions and registries only. It does not resolve artifacts,
construct a Source/engine, call the guest, import a heap/store or authorize a native
operation. The loader rejects existing package namespaces before loading any unit:
never redefine deftypes or private registries under a live Run/ModuleLease/Base.
For a retained REPL with old namespaces already loaded, compare source/provenance
and validate the changed helper integration separately rather than invoking this
loader over the live session.

## External admission remains required

The caller must supply independently hash-checked inputs for the pinned Lean
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` source, accepted original code catalogue
and explicitly authorized source overlays, 534-global runtime companion, matched
Prelude paired artifacts, format-2 kernel store and live resource lease, compiled
layout/bridge receipts, actual original finalizer execution and native/host/export
policies. The fixed module's valid legacy source header is:

```lean
prelude
import Init.Prelude
```

Requested import flags are `[false,true,false]`; pinned Lean's private import
loading yields effective `[true,false,false]`. A genuine parser/header witness
must agree. Stored declarations, matching shapes, source hashes and module data
alone do not establish strict proof replay, guest environment association, finalized
lineage, generated IR authority or executable project loading. Runtime owners and
source/store leases must remain alive through explicit resumable cleanup.

## Authenticated demand injection

`ansatz.research.ir.authenticated-demand/attach` returns the actual driver with
explicit `:resolve-row!` and `:check-source!` policies. The resolver receives that
driver and exact typed Name, authenticates bounded raw original bytes/SHA/Name
against its accepted source and authorized overlays, and returns `:row`, `:sha256`
and `:source-binding` (the actual SourceBinding). The source guard enforces the
actual live source/receipt/resource authority on every lookup, including memo hits.
These callbacks are trusted adapter policy, not booleans supplied as evidence.
The helper itself does no selected-overlay discovery and reads no implicit target
paths. Existing admitted resolver logic can be wrapped explicitly:

```clojure
;; authenticated-resolve! and check-live-source! belong to the caller's
;; already admitted source policy; this package does not invent them.
(def demand-driver
  (ansatz.research.ir.authenticated-demand/attach actual-driver
    {:resolve-row! authenticated-resolve! :check-source! check-live-source!}))
```

The sequential probe preserves its `host-helper` call facade but dispatches only
to these namespaced functions, with no ambient `user` Vars. Header memo reuse
checks actual SourceBinding, CAS SHA, typed Name, full immutable raw declaration
(including extern entries/info) and evidence metadata. Body materialization uses
the existing actual CodeRequest and engine lineage checks. This is code demand,
not permission to implement an extern or execute a hidden callback.

## Verification and limits

Load existing baseline, array and pointer check definitions, then call
`load-models!`. Each model namespace exposes `check!`; demand and node decoder checks take the
caller's actual compiled `basis` argument. Decoder checks use the existing
`fixtures/` directory when run from `experiments/lean-ir`. Model definitions do not execute tests on load.
They cover actual tiny Header/CodeRequest demand and memo rejection, issuance
refusals, lifecycle/owner transitions, base/domain/CI identity,
strict local branch checking and bounded borrowed decoding. Model capability
stubs grant no real source/Run/Module/Base or guest association authority.

Before integration, run all copied focused checks against the current compiled
Java basis, plus the actual retained source route through valid header parsing,
original finalization, strict checking, IR sealing/linking, JVM invocation, EOF
and complete owner retirement. The packager ran only mechanical hash comparisons,
path audits and delimiter validation; no JVM/native process or fresh standalone
boot was run. Existing runtime successes are external receipts, not replayed by
loading this package. Website build/browser suites are unrelated to these research
source additions and were not run.
