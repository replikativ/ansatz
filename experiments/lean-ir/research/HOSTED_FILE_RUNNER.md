# Prepared hosted file runner

`prototype.hosted-file/run-file` combines the existing frontend, strict final-unit
installation, explicit guest initialization, and boxed raw calls. It does not
prepare the bootstrap or imported Environment. `export-module` wraps the separate
real guest source-module exporter; it does not write or publish a module.

The caller supplies these actual prepared inputs:

| Input | Contract |
| --- | --- |
| `:session` | Raw session with the file helper and guest Name encoder already linked, and the required host capabilities bound |
| `:world` | Immutable world matching that session; bootstrap actions and intended imported environment already prepared |
| `:catalogue` | Explicit trusted pinned catalogue backing the program and imported code |
| `:environment` | Borrowed owned guest Lean Environment, associated with the checked kernel as required by command admission |
| `:options` | Borrowed owned guest Lean Options reference; no fabricated host map |

The ordinary imported-file path prepares imports using `module-import`, then
passes its actual Environment. The small prelude campaign instead uses the
existing `lean/HostedFileProbe.lean` helper `HostedFileProbe.preparePrelude`.
Given an already linked session/world/catalogue, its owned result can be unpacked
exactly as in the successful campaign script:

```clojure
(require '[prototype.machine :as m]
         '[prototype.raw-interop :as raw]
         '[prototype.hosted-file :as hosted])
(import '[ansatz.kernel Name])

;; prepared-session/prepared-world/prepared-catalogue come from explicit
;; bootstrap/link/import preparation. This helper is for the prelude probe only.
(def prepared
  (let [r (raw/call prepared-session prepared-world
                   ["str" ["str" ["anonymous"] "HostedFileProbe"] "preparePrelude"]
                   [m/erased])
        world (:state r)
        wrapper (:value r)
        pair (first (:fields (m/node world wrapper)))
        [environment options] (:fields (m/node world pair))]
    {:session (:session r)
     :world (-> world (m/retain environment 1) (m/retain options 1)
                (m/release wrapper 1) (assoc :result 0))
     :catalogue prepared-catalogue :environment environment :options options}))

(def module-name (Name/mkStr Name/ANONYMOUS_NAME "PreludeIdentity"))
(def answer-name (Name/mkStr Name/ANONYMOUS_NAME "answer"))
(def compiled
  (hosted/run-file prepared
    {:path "fixtures/hosted/PreludeIdentity.lean"
     :module-name module-name :roots [answer-name]
     :initialization :defer
     :calls [{:name answer-name :args [m/erased 42]}]}
    {:install-options {:research-traps? true}}))

(:success compiled)
(:diagnostics compiled)
(mapv :value (:call-results compiled)) ; [42] for this fixture
```

For editor input, replace `:path` with `:text source-text` and
`:file-name "PreludeIdentity.lean"`. Names are kernel `Name` values; the runner
uses real guest Name constructors and cached hashes. It does not guess module
names from paths, parse dotted names, or infer imports from the filesystem.

Every request must choose `:initialization :defer` or `:run`. Compilation always
installs code without running module initializers. `:run` subsequently executes
the admitted unit's actual guest plan through `eval-const/run-initializers`,
including its completion guards and evidence. Source-time macro registration is
not repeated. A deferred unit with pending initializers may be inspected but
cannot run requested calls through this convenience runner.

Successful results retain the frontend fields, updated `:world` and `:session`,
owned `:environment`, `:initialization-state`, and ordered `:call-results` entries
containing `:name`, `:target`, and owned raw `:value`. Always keep the returned
session with its world: macro evaluation may link more code. Release returned
references through the machine ownership API when finished. Original prepared
input owners remain borrowed. Each requested call transfers its raw argument
owners only when that call starts; a diagnostic compilation does not consume
unstarted call arguments. Earlier returned call values remain owned if a later
call fails and appear in exception data alongside the latest checkpoint/session.
No failure authorizes replay of external effects.

To export the resulting classic module, first explicitly link
`SourceModuleExport.exportClassic` and its required guest export aliases into the
resulting session/world, following `source-module/with-ir-export-aliases`. Then:

```clojure
;; export-prepared contains that matching session/world and compiled Environment.
(def exported (hosted/export-module export-prepared module-name))
(:status exported)
(:metadata exported)
;; :module-data is owned on :ok; :io-result is owned on :io-error.
```

No native Environment pointer is supplied, and the runner never invokes a native
compiler for an input file. Helper preparation and source-export linking remain
explicit because they are capabilities, not incidental filesystem discovery.

## Finishing an independently completed compilation

The normal runner shares two explicit finishers with manually staged callers:

- `frontend/finish-compilation-refs` accepts an actual completed raw
  `compileImportedFileState` result, the original file name and borrowed guest
  roots, and the original installation configuration. It checks the done/result
  and session/function identities, retains the returned Environment before
  releasing its IO wrapper, validates the envelope, and strictly installs code.
- `hosted/finish-file` accepts that compiled result and the original execution
  request. It runs the same explicit initialization and admitted calls as
  `run-file`, without reading source or compiling again.

```clojure
(require '[prototype.frontend :as frontend])

;; completed-raw is the actual result of an independently completed guest call.
;; original-roots remains borrowed and live throughout this finishing call.
(def compiled
  (frontend/finish-compilation-refs completed-raw
    {:file-name original-file-name :roots original-roots}
    original-configuration))

;; Only when the original structured-name wrapper left these temporary owners:
(def compiled
  (update compiled :world #(-> % (m/release original-module 1)
                                  (m/release original-roots 1))))
(def loaded (hosted/finish-file compiled original-request))
```

A failed raw callback snapshot is not a completed file result. Neither finisher
resumes a callback or permits an automatic retry. A caller must first establish
that any proposed continuation preserves the actual world, session, resources,
control state, and ownership, and that replaying a failed prefix is justified by
its effects. Temporary-owner cleanup consumes only the caller's actual original
owners; immutable diagnostic alternatives are separate branches.

The [actual ordinary macro result](../measurements/hosted-ordinary-macro.json)
completed this staged path after a reviewed strict-metadata failure at cumulative
guest step 642,225,888. The original callback had borrowed environment/options/name
arguments and stopped in reuse validation before installing the new unit or
executing its value. Its trusted witness/exporter prefix was reviewed as pure.
The retained exporter IO String owner was released once, the same host request
continued, and its completed raw compilation result passed through both
finishers with temporary-owner cleanup between them. The resulting macro call
returned `[42]`, no diagnostics, no pending initializers, and initialization state
`ready`, without replaying earlier source elaboration or compiling the input
natively. The [recovery log](../target/frontend-resume-macro-reviewed.log) records
that execution.

Its **100,724.634313 ms is the resumed segment only**, not fresh whole-file macro
compilation time. This establishes the concrete macro recovery, not arbitrary
handler retry safety. Ordinary-file interop has the separate concrete result
below. Separate focused
staged-finisher tests pass **23 tests / 342 assertions** on modeled helper
outputs and captured IR; their pause/continue, result validation, ownership,
initialization, and completed-call error checks do not themselves establish
native frontend compatibility.

## Ordinary-file host callback evidence

[OrdinaryInterop.lean](../fixtures/hosted/OrdinaryInterop.lean) passed an actual
fresh file run from the strictly associated, full-Init prepared environment.
Its polymorphic `@[extern "ansatz_host_identity"]` opaque and ordinary Lean
wrapper were compiled and installed through the guest frontend. An explicit
Clojure capability received two calls, one for Nat `42` and one for Unicode
String `"Lean ↔ Clojure: λ 🦉"`. It validated the values without consuming their
borrowed views, then returned the same owned payloads. The caller decoded each
returned value and released its owner once.

The [measurement](../measurements/hosted-ordinary-interop.json) records both
results, exactly two host calls, no diagnostics, zero pending initializers,
initialization state `ready`, and no native per-input compiler. The
[actual execution log](../target/frontend-run-ordinary-interop.log) is distinct
from helper-model tests. **45,138.887217 ms** covers the prepared JVM file run,
initialization, and both calls with compile threshold 64. This is a whole file
attempt from a prepared runtime, whereas the macro's 100,724.634313 ms above is
only its resumed segment. Neither observation is a fresh-bootstrap or
steady-state throughput benchmark.

This establishes the concrete owned Lean↔Clojure identity callback for Nat and
Unicode String, not arbitrary native ABI compatibility. Native Lean-produced
bootstrap and verified import artifacts remain required. These ordinary interop
files borrow the already finalized Init environment. A later separate bounded
[ordinary A→B result](../measurements/hosted-ordinary-library-b.json) imports A's
actual ModuleData alongside the verified Init closure, strictly checks the whole
65,995-constant map and exercises the genuine imported-source witness before
calling B. That result required a reviewed header-association fix; its timing
covers completion only, without guest compilation/finalizer replay. It establishes
this two-source-module case, not arbitrary package imports. See
[the import contracts](HOSTED_SOURCE_MODULES.md) for exact ownership/provenance.
The earlier prelude A-to-B result retains its separate narrower scope.

The separate [heap-String fork observation](../measurements/hosted-ordinary-interop-heap-forks.json)
uses that already compiled ordinary wrapper through `finish-file`, without reading
or compiling source again. A genuinely owned guest `:string` Ref (tag249, RC1)
was passed through the exact owned extern ABI in each of two independent forks.
Both returned the same input Ref/id with RC1; each returned owner was released
once. Releasing branch A left branch B and the seed unchanged, and releasing B
also preserved the seed. There were exactly two host calls, no diagnostics and no
pending initializers. **1072.785908 ms** covers these calls and checks from a
prepared compiled runtime, not frontend compilation or fresh bootstrap.

The text was `"Owned heap String: λ 🦉"`. The heap layout uses the existing
validated text-backed String profile; it does not represent a native address,
capacity, reference counter or foreign allocator. This strengthens the concrete
guest heap ownership/fork evidence without claiming arbitrary native FFI or
effect isolation. The current [experiment regression](../measurements/hosted-source-header-regression.json)
passes **691 tests / 58,784 assertions**, with all 192 recorded source/test hashes
unchanged. This is the experiment JVM suite, not parent Ansatz source/AOT/JAR
validation. Actual hosted observations remain distinct from modeled tests.

A [proposed resident facade](RESIDENT_FRONTEND_API.md) would package this explicit
prepared-context lifecycle, typed calls and binding checks. That API has not been
implemented; the current runner's preparation/import obligations above remain.

Focused tests use a clearly labeled frontend-envelope helper model, the captured
`fixtures/hosted/PreludeIdentity.ir.jsonl`, and the real guest Name-encoding IR.
They verify orchestration, owners, fork isolation, actual guest initializer
execution, and error recovery without rebuilding full Init. These tests do not
claim a new full-frontend or source-module compatibility result.

The public runner also passed the actual hosted frontend, separately from those
focused helper models: the valid prelude file returned 42, and
[`HostedDiagnostic.lean`](../fixtures/hosted/HostedDiagnostic.lean) returned the
same unknown-identifier position as the separate native oracle (line 2, column
43). The failed run retained its partial Environment, returned no calls, and
installed no final bundle. See the [actual observation](../measurements/hosted-file-runner.json)
and [reusable REPL probe](../scripts/hosted-file-probe.clj). No native compiler
ran for either input on the hosted execution path.
