# Wandler clean reimplementation — staged plan

Guided by `lean-wandler` (the clean native-Lean re-expression of wandler), rebuilding `wandler`
on a clean base over the `ansatz` kernel, with ansatz co-evolving to close the affordance gaps
just-in-time. This plan is grounded in three audits (lean-wandler blueprint, wandler coverage map,
ansatz affordance scorecard) + the Mathlib-modularity research. Companion to `docs/RETHINK.md`.

## 0. Principles (the non-negotiables)

1. **Strangler, never big-bang.** Current wandler (17,358 LOC, green) stays the working **reference +
   feature source**. We build the clean core in a fresh namespace tree *alongside* it, port one
   lean-wandler module at a time foundation-first, and **cut over only when the new core passes a
   differential harness against the old**. There is never a window where nothing works.
2. **Differential testing is the safety net.** For every ported module: run the same query / law /
   plan through BOTH old wandler and the new module and assert (a) identical optimized plan, (b)
   identical executed result, (c) the proof still `check-constant`-verifies. This is what lets us
   delete 17k LOC of working code without fear.
3. **Realistic target.** "As thin as lean-wandler" (1,590 LOC) is NOT reachable — that number rides
   Mathlib + Lean's compiler, which we self-host. Target = **clean, systematic, and as thin as a
   self-hosted-kernel Clojure impl can be**. Honest outcome ≈ 11–12k (down from 17.4k), ~30% thinner
   AND much cleaner, AND ansatz matured. The win is maintainability + matching lean-wandler's
   *structure*, not its raw count.
4. **Own a small algebraic prelude; do NOT package Mathlib.** Research verdict: the Lean community
   keeps Mathlib monolithic *by design* (one canonical Int/Real; monorepo refactorability) and it
   doesn't run on our kernel anyway (we consume it only as an export store). lean-wandler's whole
   `Laws/Frame` is 115 LOC citing ~a dozen Mathlib lemmas. So we build a **small, layered,
   self-contained `ansatz.prelude`** (the Batteries-tier between the Init store and wandler), Init-only,
   ~a few hundred LOC. The Mathlib export store stays the breadth *oracle/fallback*, and lean-wandler's
   `simp only [...]` sets are the checklist of what to reformalize first.
5. **Core-first, breadth-after.** Port the lean-wandler-covered core (Reducer→…→Surface) on the clean
   base first; re-add the extras lean-wandler lacks (records, DBSP, streams, modes, inference, engine
   bridges) afterward, each as its own module on the clean foundation.
6. **ansatz co-evolves just-in-time.** Each compiler gap is closed immediately before the first module
   that needs it — the module you're authoring tells you exactly which lemma/feature the gate is
   blocking. Each ansatz change ships with its own test + both-suites-green gate.

## 1. The three pillars (interleaved, not sequential)

- **Pillar A — ansatz compiler gaps** (small, M-effort, slotted where first needed):
  - **A1. Level-polymorphic + un-gated isDefEq simp matching.** Add level-metavars to
    `ansatz.tactic.unify/is-def-eq!` (currently only checks `lvl/level=`), let `try-theorem` handle
    level-poly named lemmas, and widen the proj-headed gate (`simp.clj:1075`) carefully (keep the
    optimizer's cost-based selection stable — that gate exists because un-gating perturbed
    `tropical-frame-index`). **Needed at:** first carrier-generic typeclass law (Phase 4, Laws/Frame).
  - **A2. Congruence-under-a-SOAC-binder** (`List.flatMap_congr` / map/filter congruence under the
    step-λ). Gives simp the implicit `congr`/`funext` the relational laws need. **Needed at:** Phase 4,
    Laws/Rel (~30% of relational rewrites). Also yields a user-facing `congr`/`funext`/`ext` tactic.
  - Deferred / off-path: typeclass diamonds + C3 (only if the class hierarchy needs a diamond — the
    Monoid⊂Semiring chain doesn't); grind theory-combination (wandler proofs use simp/omega/induction).
- **Pillar B — the owned `ansatz.prelude`** (Batteries-tier; Phase 1, then grown per-need):
  - `prelude.order` (relations/decidable order, only what's used)
  - `prelude.algebra` — `WAddMonoid ⊂ WSemiring` (bundled classes via `a/structure :extends`; rebuild
    the existing wandler `semiring_class`/`algebra` here, cleanly)
  - `prelude.list` — the List big-operator lemmas lean-wandler cites: `sum_map_mul_left`/`_right`,
    `map_flatMap`, `sum_append`, `sum_map_sum_comm`, the map/filter/flatMap fusion lemmas. Init-only,
    tactic-scripted, each `check-constant`-verified. This is the ~dozen-lemma core of the "Mathlib
    advantage" for this domain.
- **Pillar C — the strangler reimplementation** (Phases 2–8 below).

## 2. Build sequence (foundation-first; lean-wandler's order)

Each phase: what to build · ansatz affordance it needs · differential gate · LOC note. Targets from
the coverage map (covered-core ≈ 8,300 → ~5,800; cruft-in-core ≈ 2,400 → ~1,100).

**Phase 0 — Scaffolding & the differential harness.**
- New clean namespace tree (strangler) alongside current wandler; mirror lean-wandler's module layout.
- Build the **differential harness** first (run-through-both + assert plan/result/proof parity). This
  is the gate every later phase reports to.
- Decide repo layout + prelude home (recommend `ansatz.prelude.*` in the ansatz repo).

**Phase 1 — `ansatz.prelude` (Pillar B).** order → algebra (WAddMonoid/WSemiring) → list big-operator
lemmas. **Slot A1 (level-poly isDefEq) here** — needed the moment we author carrier-generic class laws.
Gate: every lemma verifies; the set covers lean-wandler's `simp only` citations. ~few hundred LOC.

**Phase 2 — wandler core foundation.** (lean-wandler: Reducer, Monoid, Lower, Par/ParArray.)
- Reducer (CPS, fusion = `rfl`) — from `reducers.clj` core, drop breadth.
- Monoid-fold licence (`foldl_split`) — from `prelude.algebra`.
- Lower (the `define-csimp` certify→swap seam) — HAVE.
- Par / ParArray (monoid-proof-gated parallel fold; unboxed array path) — from `runtime.clj`.
- Gate: differential vs old wandler on fold/sum/parallel.

**Phase 3 — Data + fusion laws + certify/lower seam.**
- Data: `kmap` (verified finite Map, NodupKeys) — keystone (45 test files); port clean, keep intact.
- Fusion laws (map_map/filter_filter/foldl_map/filterMap) — from `prelude.list`.
- Optimize certify+lower seam: `optimize/certify.clj` (`verified-rewrite?` kernel gate) + install seam.

**Phase 4 — The relational law library (the big LOC win).**
- **Slot A2 (congruence-under-binder) here.**
- Laws/Frame: FAQ frame algebra over `prelude` Semiring — **tactic-scripted** (1527 → ~350).
- Laws/Rel: defunctionalized combinators (`aggJoinSum`/`starJoinSum`/`chainJoinSum`/`mmul`) +
  first-order frame/reorder/FAQ/matrix laws — tactic-scripted (1038 + 828 → ~900).
- This is where WSemiring + A1 + A2 pay off and the laws become Lean-thin (the ~2,300-LOC cruft win).
- Gate: same laws install, same proofs `check-constant`-verify, differential on certified rewrites.

**Phase 5 — Optimizer.** (Optimize/Physical, Cost, EGraph, Search, Pipeline.) Port `optimize/*.clj` +
`plan.clj` — mostly genuine logic, cleaned, structure preserved. Ensure grind tactic parity for the
e-graph path. Gate: differential on every strategy (reorder/factor/grace-hash/pre-agg/frame/hoist) +
cost-based selection (watch the tropical case — A1's gate-widening must not flip it).

**Phase 6 — Surface core.** (Surface/Value, Query.) Collection verbs + relational verbs (the most-
exercised surface, keep intact) + dynamic EDN `Value` front door. Gate: differential on the surface
test corpus.

**Phase 7 — Cutover.** When the new core passes the full differential harness + a green suite, swap:
new core becomes `wandler`; old core retired to a tag/branch as the reference. One commit, reversible.

**Phase 8 — Re-add breadth on the clean base** (each its own module + tests, each independently
droppable; ~6,700 LOC, minus drops):
- Records vertical: records + malli bridge + refine/Subtype + record-fusion.
- DBSP/incremental: dbsp + zset + dbsp_stream/group/recursion + mode-lattice/∂ + live.
- Streams: stream coalgebra + stream surface + fork + JIT(stream/pgo/estimate).
- Inference/probabilistic: semiring `Rel A S` + dist/giry + WMC(+logicng) + lens.
- Engine bridges/backends: datahike + stratum + spindel + raster + simd.
- **Drop outright** (audit-confirmed dead/orphaned): `regex.clj` (0 deps, 0 tests), `reducers/affine`
  (0 deps), `surface/vocabulary.clj` (docs-only metadata). ≈ ~400 LOC removed for free.

## 3. Risk management

- **Old wandler green throughout** = the oracle. Never deleted until Phase 7, kept as reference after.
- **Differential harness gates every module** — plan + result + proof parity, not just "tests pass".
- **Both suites green after every ansatz change** (A1/A2 land with their own tests first).
- **A1 gate-widening is the one delicate spot** (optimizer rewrite selection). Treat it like the
  tropical regression we already fixed: widen the proj-gate incrementally, full wandler suite each step.
- **No silent feature loss** — the must-keep inventory (coverage map §2) is the checklist; anything
  intentionally dropped is logged (regex/affine/vocabulary).

## 4. Realistic outcome

| | now | after |
|---|---|---|
| covered-core | ~8,300 | ~5,800 (clean) |
| cruft-in-core (laws authoring noise) | ~2,400 | ~1,100 (tactic-scripted) |
| extra breadth | ~6,700 | ~6,300 (drops: regex/affine/vocabulary) |
| **total** | **17,358** | **~11–12k** |
| **structure** | organic | mirrors lean-wandler, systematic |
| ansatz | 2 simp gaps open | A1+A2 closed, matcher Lean-faithful |

Not 1,590 (inherent: self-hosted kernel + own runtime + broader surface than lean-wandler), but ~30%
thinner, far cleaner, and ansatz materially more capable as a by-product.

## 5. Immediate next steps (the on-ramp)

1. **A1 — level-poly isDefEq** (ansatz; ships first, has standalone value, low-risk with tests).
2. **Phase 0 harness + Phase 1 `ansatz.prelude`** (order→algebra→list lemmas), validated against
   lean-wandler's lemma checklist.
3. Then Phase 2 onward, A2 slotted at Phase 4.

## 6. Open decisions (confirm before Phase 0)

- **Prelude home:** `ansatz.prelude.*` (recommended, Batteries-tier) vs a separate lib.
- **Clean tree location:** new namespaces in the wandler repo (recommended, strangler) vs a fresh repo.
- **Breadth scope:** confirm the must-keep extras (DBSP/modes/inference/bridges are substantial; some
  may be research-only and could stay on the old branch rather than be re-added).

## 7. CONFIRMED decisions + the FAQ-driven aggregate-level refinement (2026-06-18)

**Decisions (confirmed):**
1. Prelude home = **`ansatz.prelude.*`** (Batteries-tier, ships with the kernel). The aggregate-level
   relational core makes the algebra/list big-operator lemmas the real foundation — they belong with
   ansatz, not wandler.
2. Clean tree = **fresh namespace tree inside the wandler repo** (strangler; old `wandler.*` stays the
   green oracle). Working name `wandler.clean.*` mirroring lean-wandler's module layout (reducer /
   monoid / data / laws.frame / laws.rel / optimize.* / surface.*).
3. Showcase breadth = **core spine (surface + optimize/laws + exec) + records/malli**. DBSP / streams /
   modes / inference / engine-bridges (datahike/stratum/spindel/raster/simd) are re-added on the clean
   base in Phase 8 OR left on the old branch as research — NOT part of the first clean showcase.

**The aggregate-level refinement (supersedes the Perm-heavy framing of Phase 4):** the FAQ investigation
(see [[wandler-perm-prelude]], the three studies) proved the materialized join LIST is NOT load-bearing
for the planner — every optimizer use of join-commutativity is on an AGGREGATED result (`length`/`foldl`
over the join), and the raw bag-`Map.join_comm` law is used in ONE place (`prove-join-length-comm`)
purely to manufacture a `length`-level `Eq` bridge. lean-wandler proves the SAME reorder with ZERO
`List.Perm` — `aggJoin_reorder` (Wandler/Laws/Frame.lean:95) goes `aggJoin_split` both orders →
`sum_filter_map` → `sum_map_sum_comm` (Fubini) → `eq_comm`. ⟹ **the clean relational core reasons
AGGREGATE-LEVEL from the start; the entire `List.Perm` cluster is RETIRED, replaced by one Fubini lemma.**
Consequences: Phase 4 shrinks further than the table in §4 (no Perm combinators to port); the
`wandler.prelude.perm` lemmas become latent foundation (only needed for a future order-sensitive
ROW-returning reorder the planner doesn't attempt); de-duplicating the old Perm cluster is CHURN-to-skip
(the clean core deletes it). The join in the clean core is lean-wandler's flatMap-based `joinOn`
(xs.flatMap (fun x => (ys.filter (lf·=kf x)).map (x,·))), aggregated by a `WAddCommMonoid` fold.

**On-ramp status (the A1 step is DONE + more):** shipped faithful ansatz tactic capabilities this round
— apply solves universe-level mvars; apply threads shared metavars across sibling goals (Lean's one
MetavarContext); solve_by_elim is a backtracking DFS; local hypotheses shadow globals as lemma args;
higher-order surface goals (`[f :- (=> α β)]`, `[h :- (forall [x :- α] …)]`, `(lam …)` in goals)
confirmed working. ansatz `src/` is clean (agent-confirmed). So ansatz is in shape; remaining gap A2
(congruence-under-SOAC-binder) stays slotted at the relational-laws phase, closed just-in-time.

**Immediate execution order (refined):** Phase 0 (clean tree skeleton + differential harness) → Phase 1
`ansatz.prelude` (order → WAddCommMonoid/WSemiring → list big-operators incl. the keystone Fubini
`sum_map_sum_comm` + `sum_flatMap` + `sum_filter_map`) → prove the aggregate-level `aggJoin_reorder`
(no Perm) as the thesis-validating keystone of the clean relational core.

---

## 8. STATUS (live)

**Phase 1 — DONE.** `ansatz.prelude` complete + kernel-checked: `ac` (op_left_comm/op_medial), `algebra`
(WAddMonoid/WSemiring), `list` (`wsum` + `wsum_map_mul_left`/`_add`/`_const_zero`, Fubini
`wsum_map_sum_comm`, `wsum_append`/`_flatMap`/`_flatten`, `sum_filter_map`). The thesis keystone
`aggJoin_reorder` (aggregate-level join commutativity, **NO List.Perm**) is PROVEN + relocated to the
clean tree `wandler.clean.laws.frame` (with `aggJoin_split`). Pillar A: A1 done; split S3 `cases-eq`,
faithful `reduceIte`, `rw`, binder-zonk all shipped; A2 found unneeded. ansatz suite 482/0.

**Phase 0 — DONE.** Clean tree `wandler.clean.*` stood up; **differential harness** `wandler.clean.diff`
built (pure lib): the three parities (a) PLAN `plan-parity` (vs `wandler.core/explain`), (b) RESULT
`result-parity`, (c) PROOF `proof-gate` (`check-constant` over clean laws), + the combined `differential`.
First live gate `wandler.clean.diff-test` (3 tests/13 assertions): (c) all clean laws verify; (b) the
certified optimizer preserves the result (fused ≡ naive ≡ clojure.core); (a) and it actually changed the
plan (fewer passes, kernel-certified). (a)/(b) take real old-vs-clean subjects as Phases 2+ land.

**Phase 4 (frame cluster) — REDO not migrate (decided).** The #146 "foldl cluster" is the Map-based FAQ
frame (`Map.foldl_join_sum_factor`/`Map.foldl_join_frame`, ~400 LOC of explicit term-building). Rather
than line-by-line migrate it, we REDO it in the aggregate (wsum) formulation — fundamentally thinner
(lean-wandler proves the same FAQ frame in ~3 lines). `wandler.clean.laws.frame` now has the three core
aggregate laws, all thin over the prelude + kernel-verified: `aggJoin_split` (FAQ factorization),
`aggJoin_factor` (separable-weight frame, `rw aggJoin_split` + `simp wsum_map_mul_left`),
`aggJoin_reorder` (join commutativity, NO Perm). DEFERRED: `aggJoin_factor_index` (the pre-agg
`sumByKey` index) — needs the kf/lf/DecidableEq key-structured join layer (the abstract-predicate form
deliberately omits it); fold into the clean join surface (Phase 6) + runtime (Phase 2) where the
O(distinct-keys) materialization actually lives.

**The rule going forward:** REDO where a cleaner aggregate form exists (frame/FAQ done; Perm retired);
COPY verified-as-is only what's irreducible + lean-wandler lacks; don't line-by-line migrate (its
validation purpose is spent).

**Phase 2 — STARTED.** `wandler.clean.core.monoid` (mirrors lean-wandler `Monoid.lean`): the
PARALLEL-FOLD LICENCE — `foldl_hom` (`ys.foldl op a = op a (ys.foldl op e)`, induction generalizing a
+ controlled rw chain) and `foldl_split` (`(xs++ys).foldl = xs.foldl ⊕ ys.foldl`, one line
`simp [List.foldl_append, foldl_hom]`), both thin over the prelude WAddMonoid + kernel-verified. This
is the proof lean-reducers omits — the associativity proof IS the fork-join certificate. Plus
`split_certificate` (the licence CONSUMED: fold halves at any split + combine = sequential fold; thin,
`rw <- foldl_split` + `take_append_drop`). monoid_test green; full wandler suite 350/1588/0.
**ANSATZ GAP FIXED (e3ffaf5):** `a/defn` structural recursion now supports a recursive call that
TRANSFORMS a carried arg — `replace-self-ih` accepts the param-prefix self-call PLUS extra trailing args
(the extras applied to the field's IH = Lean's `brecOn` function-valued-motive encoding). The recursion
rides the motive, not a fixed param; sound because a non-function motive makes `(IH extra)` ill-typed →
`check-constant` rejects. Faithful at the ENCODING level (curried surface = Lean's exact term); full
SURFACE parity (uncurried auto-generalization) is a further `compile-match-term` change, deferred.
**Phase 2 — Par DONE.** `wandler.clean.core.par`: `parFold {S} m depth : List S → S` (curried
divide-and-conquer, recursion transforms the carried list) + `parFold_eq` (parallel ≡ sequential, by
proof, consuming `split_certificate`), both kernel-verified. Suite 351/1591/0. REMAINING Phase 2 =
Reducer (CPS fusion = rfl) / Lower (HAVE) / the @[csimp] Task lowering (runtime phase).

**Phase 3 — fusion satisfied; data/certify deferred-clean.** The deforestation laws (`map_map`,
`filter_filter`, `foldl_map`, `map_flatMap`/`flatMap_map`, `filterMap_eq_map`/`filterMap_filter`) are
FREE from Init — `wandler.clean.laws.fusion` CITES + fail-fast-GATES them (no re-proof); fusion_test
green. The owned single-pass `map∘filter→filterMap` is an OPTIMIZER codegen rewrite (Phase 5), built from
the two filterMap Init laws. Data (`kmap`) = copy-clean, deferred to cutover (it's already clean + the
aggregate relational core doesn't need it as a LAW). certify/lower seam = HAVE.

**Phase 5 — the optimizer port (decided: ALL functionality, clean, staged + harness-gated).** Old
`wandler.optimize.*` is ~2,238 LOC; lean-wandler's `Optimize.lean` is just the certify+`@[csimp]` seam
(the rest is wandler BREADTH lean-wandler lacks). Port rule: IR-AGNOSTIC pieces copy-clean (verbatim,
ns-only retarget); LAW-COUPLED relational strategies REDO on the aggregate `aggJoin_*` laws (so we don't
re-import the retired Map cluster). Stages, each a `wandler.clean.diff` differential vs old = oracle:
- **5.1 DONE** — `wandler.clean.optimize.{certify,cost}` + facade. `certify` = the rewriter + the
  soundness gate `verified-rewrite?` (the keystone; `optimize` = fuse + self-certify = the deforestation
  path, end-to-end). `cost` = SOAC + cardinality. certify_test: clean fuses map∘map, proof verifies, == old.
- **5.2 DONE** — `wandler.clean.optimize.cse` (let/zeta, soundness-FREE = `Eq.refl`). cse_test: clean
  makes the same hoist/decline decision as old (declines a streaming share; barriers hoisted, covered by
  the old cse-test through the full optimizer).
- **5.3 DONE** — `wandler.clean.optimize.egraph` (equality-saturation search; clean retarget of the old
  egraph). Requires the certify/cost LEAVES directly (no facade cycle → facade hard-requires it back);
  clean AGGREGATE hoist-law set (`wsum_map_mul_left`/`_add`/`_const_zero` + `cost/cost-rewrites`). Wired
  into the driver as `optimize-cost :use-egraph?` (saturation as the search fallback; structured physical
  strategies still fire first). `saturate-and-extract` is an untrusted oracle — every extracted plan
  carries a `check-constant`-verified Eq.trans-composed proof. egraph_test: 3 tests/12 assertions green.
- **5.5 relational strategies on the AGGREGATE laws** (the real work): physical join-reorder→`aggJoin_reorder`,
  FAQ factor/frame→`aggJoin_factor` (+ the kf/lf index form). REDO targeting the List/`wsum` shape, not `Map.join`.
  - **5.5a (in progress) — the order-washing core (DONE) + the bucket bridge (next).** A real `Map.join`'s
    group_by bucket is built by `foldl (· :: ·) []` = the matched rows *reversed* (`Map.bucket_content`),
    so as a list it differs from the clean `filter`-`flatMap` form by that reversal. At the AGGREGATE
    (`wsum`) level the order washes out. The two order-washing lemmas are now PROVEN THIN + in the prelude
    (`ansatz.prelude.list`, pinned in `list_test`, suite 484/0): `foldl_cons_acc : foldl(::) acc l =
    reverse l ++ acc` (induction `generalizing acc`) and `wsum_reverse : ∑(reverse l) = ∑ l` (commutative
    monoid). These REPLACE the order-handling inside the 1527-LOC term-built `Map.foldl_join_sum_factor`.
    REMAINING bridge → the clean keyed factor law `Map_aggJoin_factor`:
    1. **thin `Map.bucket_content`** — `(lookup (kf x)(group_by lf ys)).getD [] = foldl(::)[](filter (kf x ==
       lf ·) ys)` — the group_by/lookup → filter-foldl relational lemma. Currently only the OLD term-built
       proof exists (`wandler.laws.proofs`); re-prove thin (this is the genuinely hard unit — heavier than
       5.5a's Init lemmas). NOTE `List.foldl` is `{α=acc β=elem}`, `f : α→β→α` (type args swap caught us).
    2. **assemble** `wsum (map weight (Map.join …)) = <factored>` via `simp [Map.join.eq_unfold,
       bucket_content]` → `foldl_cons_acc`+`List.map_reverse`+`wsum_reverse` (wash bucket order) →
       `wsum_flatMap` + `wsum_map_mul_left` → `aggJoin_factor`. Replaces `Map.foldl_join_sum_factor`.
    Then 5.5b wires each physical recognizer to this law (machinery copies clean, law is thin), harness-diffed vs old.
- **5.6 DONE** — the cost-search DRIVER `wandler.clean.optimize/optimize-cost`: tries the structured
  physical strategies (factor → reorder) first, composing each adopted step's proof with the fusion
  step via `Eq.trans`; falls back to equality saturation (`:use-egraph?`) or plain confluent fusion.
  cse (`try-cse`) is re-exported (soundness-free let/zeta hoist), available to compose. physical_test +
  egraph_test green.

**Phase 5 — DONE.** 5.1 certify/cost · 5.2 cse · 5.3 egraph · 5.5 physical (factor/reorder on the
aggregate `aggJoin_*` laws + the bucket bridge `Map.bucket_content`) · 5.6 driver. Full wandler suite
361t/1649a/0; ansatz 485/0. ALSO fixed two latent ansatz bugs surfaced here: env-blind synth-cache
(env-keyed now) and a lexical-scoping bug (local binders now shadow the surface vocabulary registry —
a `dec :- DecidableEq` binder was being shadowed by the clojure-decrement `dec` term-elaborator).
DEFERRED in Phase 5: `aggJoin_factor_index` (the kf/lf-keyed pre-agg `sumByKey` O(distinct-keys) index)
— folds into the clean join surface (Phase 6) + runtime where the materialization lives.

**Then Phase 6 (surface) — the cutover gate.** This is where the clean core gets a user-facing front
door (collection + relational verbs + dynamic EDN `Value`), which is also what unlocks the FULL a+b
differential parities (`wandler.clean.diff`) against old wandler on REAL subjects (today only proof-
parity (c) runs live; (a) plan + (b) result need surface-elaborated subjects).

**Phase 6 — STARTED (collection + relational front door DONE).** `wandler.clean.surface.{common,
collections,relational,core}`: clean-tree port of the old surface (IR-agnostic copy-clean, requires
retargeted). collections = ~30 collection verbs; relational = member/some/every?/distinct/sort/group-by/
vals/keys/->map/frequencies/join (emits Map.group_by/Map.join/AList.*). `core` aggregates + requires
the SHARED `wandler.runtime` codegen (auto-installs) so surface-elaborated `a/defn` bodies EXECUTE —
self-contained (as `wandler.exec.mode` already does; clean runtime is the deferred Phase-2 remainder).
`core_test`: mapv∘mapv + ->>/mapv/reduce elaborate → EXECUTE w/ result-parity vs clojure.core → clean
`optimize-cost` certifies map_map fusion; group-by/->map elaborates a Map.group_by term. wandler
363t/1655a/0. Surfaced: a/defn codegen needs the runtime lowering registered process-globally (the
ENABLING fact for lexical-scoping — local binders now shadow that registry, fixed in Phase 5).
**Phase 6 — Value front door + cutover differential DONE.** (1) `install-value!` brings up the dynamic
EDN `Value` universe (the shared `ansatz.surface.data` capability — installed, not re-ported); native
Clojure map verbs run over kernel-verified `Value`. (2) `wandler.clean.diff/clean-plan-report` gives a
`w/explain`-shaped report from the CLEAN optimizer, and `diff_test` now runs a REAL clean-surface subject
(mapv∘mapv) through BOTH old wandler and clean, asserting ALL THREE parities live: (a) plan certifies +
fuses 2→1 passes, (b) clean ≡ old ≡ clojure.core on every input, (c) the backing clean laws verify —
the first time (a)+(b) run on genuine old-vs-clean subjects (was proof-only). Hardened
`option_narrowing_test` (re-installs its Option surface; the Value `nil?/some?` exposed its load-order
reliance). wandler 365t/1666a/0.
**Phase 6 — COMPLETE.** The full clean surface front door: collections + relational + Value + the
records/malli vertical (`wandler.clean.surface.{common,collections,relational,records,malli,refine,core}`),
each end-to-end (elaborate → execute → certified-optimize), self-contained on the clean tree.
records_test: def-record lifts a malli :map, idiomatic assoc/`:field`/update kernel-verify.

**Phase 7 — cutover GATE COMPLETE; literal swap GATED ON PHASE 8.** The `cutover-differential-corpus`
(`diff_test`) runs a representative corpus of ordinary-Clojure surface queries (map∘map / filter∘filter /
map∘filter / filter→map→reduce / map∘map∘map) through BOTH old wandler and the clean surface+optimizer,
asserting for each: clean ≡ old ≡ clojure.core on a battery of inputs AND a kernel-certified clean plan.
This passing is what justifies the cutover — the clean core is a proven faithful drop-in for the old
core across the surface it covers. SOUNDNESS FIX surfaced here: `cert/optimize` now REJECTS an
unverifiable rewrite and keeps the original (never ships a `:verified? false` plan; map∘filter exposed a
partial simp normalization with a non-strict congruence proof). Tagged `clean-core-validated`.
**The literal namespace swap (clean.* → wandler.*, retire old) is NOT done — and must not be yet:** 19
breadth modules (gradual / plan / jit.stream / exec.* / inference.* / bridge.datahike / dbsp / stream /
verified / …) still depend on the OLD core (optimize/laws/surface/reducers). A swap now would break all
19 → break the build, violating §0.1 ("never a window where nothing works"). Per the plan's own
sequencing, those breadth modules are re-added on the clean base in **Phase 8 FIRST**; the one-commit
reversible swap is the Phase 8→done boundary, once nothing depends on the old core. The cutover is
*gated and proven*, not *executed*.

## 9. PHASE 8 — breadth re-add / retire the old core (live)

Strategy chosen (2026): **retarget + shared engines** — point breadth's CORE imports (optimize/laws/
surface) at the clean tree, keep genuine shared engines (runtime, reducers, plan-lens, streams).

- **8.1 ✅** clean `strings` surface + drop dead `regex`.
- **8.2 ✅** clean `option` surface → the clean surface vocabulary is COMPLETE (collections/relational/
  records/malli/refine/Value/strings/option).
- **8.3 ✅** clean `optimize-body` (the a/defn-integrated optimizer entry; direct port over clean
  cert/cost/cse/phys).
- **8.4 ✅ — the facade cutover (surface + optimizer).** Measured first (throwaway hook-flip): only 17
  assertions diverged, all wandler-side optimizer gaps.
  - **8.4a** retarget all 5 src + 24 test old-surface importers to clean, DELETE the 8 old surface
    modules (~2,400 LOC retired).
  - **8.4b** ported the greedy cost-rewrite pool (semijoin/pushdown/filterMap) + try-hoist-invariant
    into clean optimize-cost, normalized `:rewrites` labels → flipped wandler.core's optimize-hook to
    the clean optimizer. Full suite 370t/1707a/0 with EVERY a/defn on the clean optimizer.
- **8.5 (next)** retarget the direct old-`wandler.optimize` importers (bridge/gradual/jit.*/exec.*/
  inference) + core's profile-selectivity to clean; then delete old `wandler.optimize`.
- **8.6** laws (semiring_class → clean) · **8.7** delete remaining duplicated old core · **8.8** the
  literal clean.* → wandler.* swap.

zero ansatz kernel fixes needed across all of Phase 8 so far — confirming the study: the work is
wandler-side retargeting + optimizer feature-completion, not kernel.

## 10. PURIST PORT — Level 1 COMPLETE (old optimizer deleted)

Strategy: **Level 1 → Level 2, staged** (strategies/law-proofs are decoupled — strategies are
recognizers that APPLY proven laws by name).

**Level 1 — DONE.** Ported every FAQ/index strategy + the optimizer DRIVER verbatim into
`wandler.clean.optimize.faq` (clean cert/cost + shared sreg/sc); clean `optimize-cost` tries the clean
wsum aggJoin strategies then delegates to the ported driver — identical plan selection to old. Retargeted
all breadth (bridge/gradual/plan/jit/exec) + ~20 old optimizer test files onto the clean tree, then
**DELETED old `wandler.optimize` + optimize/{physical,certify,cost,cse,egraph}**. The clean optimizer
is the ONLY optimizer; a green suite (371t/1711a/0) with no old optimizer present proves clean ⊇ old.
Kept as shared engines: `wandler.optimize.plan` (the α/γ lens), `wandler.optimize.faq` (FAQ query
helpers), `wandler.laws.*` (the proven Map-cluster law engine the strategies ride).

**Level 2 — remaining.** Re-prove the keyed Map-cluster laws (`Map.foldl_join_factor`/`frame_generic`/
`sum_factor_generic`/… ~2,477 LOC in laws/relational + laws/proofs/frame) in clean AGGREGATE form (the
deferred Phase-4 keyed-index keystone), swap the strategies' law-references onto them, delete
`wandler.laws`. This is deep proof engineering (the hard part Phase 4 deferred), a substantial separate
effort. Then the literal `clean.* → wandler.*` swap.
