# Programming-model gaps — running tracker

Living list of known gaps in the verified-Clojure programming model (ansatz = kernel + Clojure↔kernel
bridge; wandler = the optimizing algebra). Update as gaps are found/closed. Each entry: what, why it
matters, where, status.

## EDN / Value / Clojure-data lifting

- **Recursive conformance WF** — FIXED (data-lifting move). The recursive `all p (cons-chain)` recurses on
  the `Value` cons-tail (a constructor arg) = structural. It was failing at WF `(sizeOf c)` because the
  generator emitted surface `and`, which expands to an `ite`/`Bool.rec` that BURIED the recursive call in a
  branch where the WF/structural analyzer couldn't see the decreasing argument. Emitting `Bool.and`
  directly (the data-lifting move's and/or/not→Bool.* rewrite) keeps the recursion visible → it now
  compiles structurally. Now total: `:vector`, nested maps, vector-of-maps, recursive registry trees all
  verify (test/wandler/value_functor_test.clj). STATUS: closed.
- **Conformance recursive path now tested** — value_functor_test exercises recursive schemas through the
  #8 functor (each kernel-verifies). STATUS: closed.
- **Schema bridge is two-layer (by optionality, not a gap)** — `ansatz.malli` (hard-requires malli.core:
  live registry + a/defn signatures + precise schema→type) and `ansatz.surface.schema` (schema-DATA →
  Value conformance + #8, NO malli-library dep). Merging would wrongly force the optional malli dep onto
  the no-dep conformance lane, so they stay separate. STATUS: by design.
- **Differential lane is narrow** — `check-verified!` generates only Nat/Bool/List Nat inputs; `:or`/`:enum`/
  strings/maps aren't differential-tested against `m/validate`. STATUS: open.
- **Native-Clojure-over-Value coverage** (audited). COVERED: type predicates (int?/string?/boolean?/
  keyword?/nil?/map?/vector?/set?/double?/some?/any? → v*?), `:k`/`get` (vget), `assoc` (vassoc), `count`
  (vcount), `==`/numeric compare. MISSING: `update`, `merge`, `dissoc`, `contains?`, `keys`, `vals`,
  `get-in`/`assoc-in`, `conj`/`into`, map/filter-with-destructuring over Value entries. STATUS: open
  (extend ansatz.surface.data's native surface — these are the high-value next verbs for dynamic EDN).

## Schema → type functor (#8)

- **Subtype round-trip is lossy** — `type-expr->malli` drops a `Subtype`'s predicate (opaque), so the
  functor isn't invertible on refinements. STATUS: open (acceptable per design; revisit if needed).
- **Precise lane has no `Sum`** — `:or`/`:enum` get no *precise* kernel type, only the universal
  `Subtype Value γ` (#8). This is the CORRECT model (untagged union = semantic subtyping), not a gap to
  "fix" with `Sum`; noted so it isn't mistaken for one. STATUS: by design.

## Architecture agenda (the 10-item review) — remaining

- **#5** unify the 8 `exec/*` files under one `StreamOp` — flagged lowest-value (composition laws are
  heterogeneous); the bounded win is carrier-generic algebra (extend `dbsp_group`'s pattern). STATUS: open.
- **#9** real transducer output — emit `(map f)`/`(comp …)`/`into`/`sequence` so verified pipelines compose
  with native Clojure transducers (rides on `register-lowering!`). The fusion laws ARE certified
  transducer-comp. User wants to plan the array/eager-vs-transducer tradeoff carefully first. STATUS: open.
- **#10** env-branching as first-class hypothetical worlds (`Env` O(1) fork at the surface). STATUS: open.

## Other latent items (from memory / task backlog)

- Float filter-predicates + surface unification (#51); regex OR-fusion → a/defn optimizer (#66);
  rel-laws packaging — semijoin/aggregation/join-reorder (#67); elaboration breadth — more Clojure verbs
  to kernel terms (#72); boundary normalization so shape-matching rewrites fire on any spelling (#73);
  omega reconstruction generally + verified omega prelude + re-verify shipped init (#84/#85/#86).
