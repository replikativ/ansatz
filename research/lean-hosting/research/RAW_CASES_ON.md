# RAW casesOn construction before profile sealing

`lean/KernelCasesOnRaw.lean` ports the pinned Lean 4.33.1 `cases_on.cpp`
constructor into ordinary Lean code. It operates on the original guest
`Kernel.Environment`, `Name`, `Level`, `Expr` and `LocalContext`. Metadata,
`letE.nondep`, binder information and raw universe constructors do not pass
through the Java checking projection.

Its emitted ABI matches `Lean.mkCasesOnImp` exactly: owned Environment,
borrowed Name, owned `Except Kernel.Exception Declaration`. Construction does
not admit the resulting declaration. Existing kernel admission and policy checks
remain required. This component does not establish general hosted frontend
compatibility or faithful annotated inductive generation upstream of casesOn.

## Preparation

`prototype.cases-on-preparation/prepare` accepts an unsealed candidate, an
independently retained configuration and an authenticated helper source/IR
artifact. The configuration retains the exact original CAS row bytes and
`:cases-on-original-function`; explicit `nil` means it was absent from the
original independent registry. The preparer authenticates the one known original
extern and trap, checks the actual helper ownership ABI, links its complete
closure, and preserves unrelated function and binding identities.

The return value contains `:candidate`, `:configuration`, `:profile` and
`:lower-extern`. Complete **all** unsealed preparers before creating a source
graph/evaluator profile. Pass the final configuration's exact
`:consumer-extern-lower` callback as `:lower-extern` in the evaluator options to
`resident-init-prefix/prepare-source-graph-profile`:

```clojure
(require '[prototype.cases-on-preparation :as cases]
         '[prototype.resident-init-prefix :as prefix])
(def prepared (cases/prepare candidate configuration helper-artifact))
(def config (:configuration prepared))
(def eval-options
  (assoc original-eval-options
         :catalogue (:catalogue config)
         :trusted-functions (:trusted-functions config)
         :lower-extern (:consumer-extern-lower config)))
;; After any further unsealed preparation, use that FINAL configuration here.
(prefix/prepare-source-graph-profile exporter eval-options helper-configuration)
```

Actual explicit raw bindings retain precedence over the consumer fallback.
Frontend installation, evalConst installation and raw host-boundary installation
preserve the configured fallback. The original producer/CAS row stays unchanged:
the redirect is a separate trusted host configuration, checked again against
actual source rows and target ABIs on future lowering. It emits a direct guest
tail call rather than a new host callback.

A catalogue containing this capability cannot be checkpointed as a durable
producer store. Persist the reviewed preparation recipe separately and reconstruct
it after restore, before sealing. Preparation opens fresh program caches rather
than retaining compiled blocks from the replaced program. It neither initializes
modules nor replays native initializers, and does not revise historical closed
consumer contracts.

## Component evidence and tests

The native oracle checked fourteen construction cases with full `Expr.equal`
and complete Definition fields. Four input inductives were admitted by the native
kernel with metadata/Syntax payloads, dependent and nondependent lets, raw
max/imax universes and nondefault binders; both generated outputs were checked
independently. Five native error cases include unusual and Unicode Names.

The JVM matrix invokes the **original extern entry** through its guest redirect
on `:reference`, `:mutable` and `:jvm`: enum, structure, polymorphic Box, indexed
family, mutual families, nested and functional recursion, Prop, unsafe, and four
annotated fixtures. It compares native output definitions, checks imported raw
annotation fingerprints, and exercises three hosted error scenarios, borrowed
Name escape counts, repeated execution, forks, source preservation and terminal
failure ownership. The JVM tier also records execution of generated regions;
these observations are not performance benchmarks or sealed-runtime attestations.

The checked-in fixture manifest separates native oracle evidence, the original
local JVM run, and the portable regression. Compacted raw object lines are copied
byte-for-byte. Only historical `.olean` paths in the external manifest become
logical relative filenames. Deterministic gzip compression reduces fixture size;
tests verify compressed and decoded hashes and materialize bounded, test-owned
seekable files. No Lean SDK, exporter, LLVM or external image is needed in CI.
The panic controller is explicit trusted host Clojure code in a normal test-support
namespace, checked against its captured source prefix. Fixture text is not evaluated.
The fixture Environment is constructor storage only, not a checked-prefix
certificate or an admission capability.

From `experiments/lean-ir`:

```sh
clojure -J-Xmx384m -J-Xss8m -M scripts/test-cases-on.clj
```

This runs the portable fourteen-case matrix plus preparation, ABI, raw interop
and installation regressions. `bin/run-unittests` invokes this selected suite
explicitly after the core tests. The normal library source/AOT paths remain
unchanged; these are optional experimental runtime APIs.

## Attribution

The algorithm port follows Lean's pinned
`src/library/constructions/cases_on.cpp`, Copyright (c) 2014 Microsoft
Corporation, authored by Leonardo de Moura and released under Apache 2.0.
The repository's Apache 2.0 license applies to this port. Captured Lean library IR
retains its upstream Apache 2.0 licensing; it is recorded as compiler test data.
