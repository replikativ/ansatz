# Programming-model gaps — running tracker

Living list of known gaps in the verified-Clojure programming model (ansatz = kernel + Clojure↔kernel
bridge; wandler = the optimizing algebra). Update as gaps are found/closed. Each entry: what, why it
matters, where, status.

## EDN / Value / Clojure-data lifting

- **Recursive conformance WF** — `install-conforms!` for `[:vector …]`/nested maps generates a recursive
  `all p (cons-chain)` whose auto-WF measure `(sizeOf c)` "did not yield a verified WellFounded.fix
  encoding". The recursion is over a `Value` cons-tail (a constructor arg) and *should* be STRUCTURAL
  (→ `Value.rec`, no WF), so it's likely mis-routed to WF rather than a deep WF gap. **Untested** in the
  suite. STATUS: open — slated for stage 4 of the data-lifting move (fix in ansatz, with a real test).
- **Conformance recursive path is untested** — no current test calls `install-conforms!`/`compile-schema`
  despite #57 claiming "breadth + recursion + depth". Likely bit-rotted. STATUS: open (revive in stage 4).
- **Differential lane is narrow** — `check-verified!` generates only Nat/Bool/List Nat inputs; `:or`/`:enum`/
  strings/maps aren't differential-tested against `m/validate`. STATUS: open.
- **Native-Clojure-over-Value coverage** — which Clojure verbs lift over dynamic `Value` (`:k`/`get`/`int?`/
  `==`/`count`/`assoc` done; what about `update`/`merge`/`contains?`/`keys`/`vals`/nested `get-in`/
  destructuring?). Needs an audit + completion. STATUS: open (audit during the move).

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
