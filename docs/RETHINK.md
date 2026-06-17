# Rethinking ansatz + wandler — lessons from the native-Lean port

Synthesis of a research exercise: a native Lean 4 reimplementation of wandler (`../lean-wandler`)
was built to learn what "clean and direct" looks like, then those lessons were assessed against the
*actual* ansatz/wandler code (three feasibility audits, all read-only, file+line-count grounded).

**Constraint (fixed):** ansatz keeps its own self-contained, Lean-compatible kernel. We are NOT
adopting real Lean, an oracle, or a Lean→JVM compiler. The question is only: *can we build the same
thing more cleanly / more directly, with a more "normal" core and less special glue?*

## Headline finding

ansatz/wandler are **much closer to the clean target than the raw LOC gap suggested**. The audits
found the alarming items are mostly *already done* or *genuinely justified*:

- infer/check discipline is already clean (no verification leak; the lenient `inferType` is a
  faithful Lean port, used only for type *computation* — never as a validity gate).
- the two kernels exist for a real reason (open metavars + attachable context the Java kernel lacks).
- the optimizer rewrite is already L0; `define-csimp` (a faithful `@[csimp]`) already exists; the
  FAQ index certificate is already proven + `check-constant`'d; the laws are already carrier-generic
  (axioms-as-hypotheses); the proofs are already tactic scripts; `Value` already rides the core verbs.

So the program is **targeted cleanup + auditability**, not a rewrite. The one genuinely new
architectural simplification is **defunctionalization** (Item 1), and it carries real coupling cost.

## The nine items — recalibrated verdicts

Effort S/M/L/XL. "Already" = the clean pattern is largely present; work is consolidation/locking.

| # | Item | Verdict | Effort | Key finding |
|---|---|---|---|---|
| 7 | Retire FlatStore mmap experiment | **CUT** (keep `ExprStore`) | S | Dead weight: only 3 opt-in fns + 2 tests use it; PSS is the sole production path. ~1.5k Java LOC out. Safest first move. |
| 6 | Structural infer/check boundary | **RENAME-ONLY** | S | Discipline already holds; no leak found. Rename Java `inferType`→`inferTypeUnchecked`; `check`/`checkConstant` is the only validity door. No `Verified` token needed (overkill). |
| 9 | L0 hash-index certificate | **PACKAGE** | S | Chain already proven (`bucket_content`+`lookup_map_kv`+`getD_map`→`foldl_join_sum_factor`, all `check-constant`'d). Add ONE named capstone `Map.faqIndexPlan_eq_naive`; mark the `group_by→clojure hash-map` rep-swap as the one trusted seam. |
| 5 | Collapse the two kernels | **DON'T MERGE → conformance harness** | S–M (harness); L–XL (merge, not rec.) | Clojure kernel handles open metavars + mutable lctx the Java kernel has no API for. Full merge is XL/high-risk vs the mathlib gate. Instead: a test asserting `tc/infer-type ≡ Java check` + `whnf ≡ whnf` on sampled decls (trace infra already exists) — makes drift a *test failure*, not a latent gap. |
| 8 | Proof-gate codegen (L1→L0) | **CONCENTRATE, don't over-claim** | M | The kernel-term rewrite is already L0; the `Expr→Clojure` emit is irreducibly trusted *by design* (JVM semantics aren't in the kernel — lean-wandler trusts its compiler too). Win = route optimize through `define-csimp` (auditable `f=f.opt` ledger) + carve `builtin-lowerings` into a small enumerated "denotation primitives" table. |
| 2 | Tactic-script the proof library | **PARTIAL, gated on one lemma** | L | Proofs are ALREADY tactic scripts; the bulk LOC is manual goal/motive construction + case-driver boilerplate. ~60–70% can shrink to clean scripts now; **~30% blocked on a missing `List.flatMap_congr` / congruence-under-a-SOAC-binder** simp step. So: harden simp's congruence FIRST, then the rest follows. |
| 1 | Defunctionalize relational laws | **HIGH value, real coupling** | L–XL | First-order combinators (`aggJoinSum`-style) retire the need for HO/under-binder e-matching — BUT to actually delete the ematcher fork you must *also* defunctionalize the **hoist family** (`sum_map_mul_const` is what the Miller matcher was built for) AND **rework the binder-aware cost model** (`soac-depth-cost` reads the binder a combinator hides). |
| 3 | One carrier mechanism (typeclass) | **SWAP routing, not laws** | M–L | Laws are already `_generic` (axioms-as-hypotheses). Win = a `WSemiring` class + instances replacing the string-keyed registry *routing*. Per-carrier proof work unchanged. Do with/after Item 1. |
| 4 | Surface (`Value`) as a carrier | **ADDITIVE, mostly done** | M | `Value` already rides `v*` verbs through the optimizer. `malli.clj` is a separate *static-typing* path the planner needs for cost info — keep it; add Value-as-carrier alongside, don't replace (else the cost model loses field types). |

**Cross-cutting invariant:** every refactored proof/law MUST be gated on `env/verifies?`
(`check-constant`), never lenient `inferType` — this codebase has shipped lenient-masked-broken
proofs before (the #40/#41/#43 history).

## Recommended sequencing

**Phase 1 — cheap, safe, high-ratio (mostly subtraction + auditability; no architectural churn):**
1. **Item 7** — cut FlatStore (~1.5k LOC, pure subtraction, isolated).
2. **Item 6** — rename `inferType`→`inferTypeUnchecked` (lock the door that's already shut).
3. **Item 9** — package the index certificate as one named capstone theorem.
4. **Item 5(c)** — conformance harness for the two kernels (drift → test failure).
5. **Item 8** — route optimize through `define-csimp` (auditable ledger) + carve the denotation table.

Net: ~1.5k LOC removed, the kernel "straight" (one authoritative checker, drift-caught, door locked),
the trust story auditable (named L0 capstones + one enumerated trusted seam). All low-risk.

**Phase 2 — the real architectural work (interdependent, L–XL):**
6. **Item 2 prerequisite** — add `List.flatMap_congr` + congruence-under-SOAC-binder to simp (the
   one concrete blocker; the lean-wandler proofs are a *checked oracle* for the exact lemma sets).
7. **Item 2** — re-prove the law library as clean tactic scripts (now unblocked).
8. **Item 1** — defunctionalize join + hoist families; rework the binder-aware cost model; then
   delete the ematcher HO/under-binder + universe-unification fork (~150–200 LOC + the hardest
   correctness surface in the e-graph).
9. **Item 3** — `WSemiring` class + instances replace registry routing (with Item 1).

**Anytime / independent:** Item 4 (additive Value carrier).

## Authoring & dev-experience (the higher-level question: why is wandler so much bigger?)

Four causes for "wandler ≫ lean-wandler in code": (1) **borrowed substrate** — Lean's
kernel/simp/grind/Mathlib are free and uncounted (given; we keep our own); (2) **library maturity** —
Lean proofs cite Mathlib lemmas (`simp only [List.foo]`) where ansatz must prove the foundation
lemmas itself; (3) **authoring ergonomics** — the real, fixable "noise"; (4) **architecture**
(defunctionalization etc., Phase 2 above).

Cause (3) is NOT the end-user data surface (`a/defn`/`Value` are fine) — it's **proof/term
authoring**, and the audit found the infrastructure already exists; the law library bypasses it
because of ONE cascade: **`a/theorem` can't take a computed/generic goal term → generic laws are
built as raw `Expr` (`e/app*`/`e/forall'`/`e/abstract1`) → proof bodies get dragged into hand-built
`congrArg`/`Eq.trans` chains.** That forcing function is the bulk of `frame.clj`'s 1,500 lines.

### Dev-experience levers (ranked; all S–M because the bones exist)

| # | Lever | Effort | Impact |
|---|---|---|---|
| L1 | **Goal-state REPL** — `(goal-at thm-form n)` dumps `format-goals` after N tactics; `(attempt ps ['(simp …) 'omega …])` returns per-tactic closed?/state. Thin wrappers over existing `run-tactic`/`format-goals`/`solved?`. | S | **Very high** — the `lean_goal`/`lean_multi_attempt` loop; biggest felt gap. |
| L2 | **Term quotation** `(t <sexpr>)` / `(t-in ps <sexpr>)` over existing `elaborate(-in-context)`. | S–M | High — kills `e/app*`/`e/forall'` noise. |
| L3 | **`a/theorem` accepts a precomputed `Expr` goal** (`:goal-expr` / `prove-theorem*`). | S | High — removes the root forcing function; generic laws move to the surface. |
| L4 | **`WSemiring` class + projections + instances** → laws state `[S : WSemiring]`, axioms projected (= Item 3). | M | High — collapses the `hAA hZA hAZ hMA hMZ hZM` threading. |
| L5 | Surface `(laws-block …)` batching mirroring `thm!`/`admit!`. | M | Medium. |
| L6 | Structured per-position diagnostics (errors as data) for an editor overlay. | L | Med-low (L1 covers most interactive need). |

Already present (do NOT rebuild): `a/theorem` tactic surface + `simp only [...]` + combinators
(`core.clj:1692`,`:621-746`); immutable proof states + `show-goals`/`format-goals`
(`proof.clj:125`); `fork`/`auto`/`suggest` search (`repl.clj:230`); instance synthesis + `:inst`
binders (`basic.clj:322-362`, `ingest.clj:88-115`); the `elaborate-in-context` that powers L2.
Genuine inherent gap (not a lever): the **breadth** of ansatz's simp-lemma / instance library vs
Mathlib — closes only with library investment, and is why proofs stay somewhat longer than Lean's.

### Revised sequencing with dev-experience first

- **Phase 0 — dev experience (force multiplier, do FIRST): L1 → L2 → L3.** All S/S–M, infra exists,
  and they make every subsequent proof in Phase 2 dramatically cheaper to author. L1 alone gives the
  interactive goal loop.
- **Phase 1 — cheap cleanups (parallel/anytime):** Item 7 → 6 → 9 → 5(c) → 8 (as above).
- **Phase 2 — the real work, now cheap given Phase 0:** L4/Item 3 (`WSemiring`) → Item 2 (tactic-
  script the law library, now ergonomic) → Item 1 (defunctionalize + hoist family + cost-model rework).
- **Anytime / ongoing:** Item 4 (additive Value carrier); **grow the lemma/instance library** (the
  one inherent-maturity investment — the lean-wandler proofs name the exact lemma sets to target).

## What actually changes (honest accounting)

- **Removed:** ~1.5k LOC FlatStore; ~150–200 LOC ematcher fork (after Phase 2); the carrier registry
  *routing*; a chunk of proof-construction boilerplate.
- **Made auditable (not newly proven):** the L0 optimizer ledger + index capstone + a single
  enumerated runtime-denotation seam.
- **Kept (justified):** the kernel reimplementation, both kernels (with a harness instead of hand
  vigilance), the malli static-typing path, the irreducibly-trusted JVM denotation boundary.

The lean-wandler exercise's real payoff was: (a) **confirming** ansatz/wandler already converged on
most clean patterns; (b) surfacing the **defunctionalization** trick (the one new architectural
simplification); (c) providing a **checked oracle** (exact `simp only [...]` lemma sets) that
de-risks Item 2; (d) the **honest trust map** (what is L0-provable vs irreducibly trusted, and that
even a real-Lean build stops at the same denotation boundary).

### Dogfood findings (authoring a real law via L1–L3)

Authoring `List.map_append` through the new loop (goal-at → attempt → assemble) surfaced concrete
syntax frictions and fixes:

- **`a/theorem` is already Lean-shaped.** `(a/theorem foo [f :- (=> Nat Nat), n :- Nat] (= Nat (f n)
  (f n)) (exact (Eq.refl Nat (f n))))` reads like a Lean `by`-block. The streamlined surface mostly
  *exists* — the law library just doesn't use it.
- **Function-type arrow = `=>`, not `->`.** By deliberate design (#54, `arrow-glyph-no-ambivalence`)
  `=>` is THE function arrow; `->` is ALWAYS Clojure threading. My first instinct (`->`) was wrong and
  broke threading. Fix landed: the fvar elaborator's `=>` now supports **N-ary currying** `(=> A B C)`
  (was binary-only) and the `→` glyph, unifying with `arrow` — matching `a/defn`.
- **`exact <term>` was missing** from the tactic registry (only `exact?` auto-search existed). Added —
  elaborates its arg in the goal context (via the same `elaborate-in-context` L2 uses) and closes.
- **Remaining friction is library maturity, NOT syntax.** Closing the `map_append` cons case needs
  `simp` to fire `List.map_cons`/`List.cons_append` — which aren't conveniently simp-tagged in
  init-medium. This is the inherent gap (Lean cites Mathlib); it's the lemma/instance-library
  investment, separate from the levers.

So the path holds: the levers make authoring feel like Lean for *concrete* laws today; generic laws
additionally need `WSemiring` (L4/Item 3); and proofs stay somewhat longer than Lean until the
simp-lemma library grows.

### Elaborator unification — the root cause, quantified

Every dev-experience friction (arrow glyph, `exact`, the structure elaborator) traced to **incomplete
elaborator unification**. An audit quantified it: there were **3** surface→`Expr` paths —
`surface/elaborate.clj` (fvar-first, 1224 LOC, **THE** elaborator, metavars + instance synthesis,
~85–90% of the surface already on it), `surface/term.clj` (254 LOC, bvar-only, **0 production callers**),
and `inductive.clj` `compile-type` (~140 LOC, bvar, the inductive/structure field/param/index lane).
The P1–P5 unification (#102–106) moved types/proofs/WF-measures onto the fvar path but left the
inductive lane divergent.

DONE (commits e674c09, a6917d8): glyph-unified the inductive lane (`=>`/`→`/`arrow` + `:-` binders +
currying), **retired `term.clj`** (deleted, 0 callers), and **removed the `->`-as-arrow inversion**
(`->` is now threading everywhere, an arrow nowhere). Two of three elaborators reconciled.

REMAINING = the real merge (ordered, suite-gated):
- **A ✅** retire term.clj.
- **B** build `elaborate-type-in-telescope` over the fvar elaborator (install ordered binders as lctx
  fvars, elaborate, return fvar-open for `abstract-many`). Bridge pattern already exists in
  `core.clj:853` (`build-telescope-fvar`); model on `elaborate-in-context` (elaborate.clj:1159).
  Must preserve inductive self-reference (`self-const`, inductive.clj:70).
- **C** route ctor field types (`compile-fields`, inductive.clj:265) through the bridge. NOTE: the
  earlier "dependent-field de-Bruijn bug blocks WSemiring" diagnosis was WRONG (corrected 2026-06-17).
  Bisection showed BOTH kernels (Clojure `tc` + Java `TypeChecker`) admit the constructor type for a
  field that applies an earlier field (e.g. `add_assoc : ∀ a b c, add (add a b) c = …`), and the
  recursor/casesOn/recOn all build. The ONLY failure was the auxiliary `build-no-confusion-type`
  (inductive.clj:1675), now made defensive (warn+skip) — so **WSemiring is already unblocked** (commit
  1fa41d1). Step C is therefore a *cleanliness* merge (kill the `compile-type` mini-elaborator's
  hardcodes — `Eq` defaulting its type to `Nat`, arithmetic ops to `Nat`), no longer a WSemiring blocker.
  The deeper noConfusion-builder de-Bruijn fix is a separate, low-priority follow-up.
- **D** route param + index types through the bridge (mechanical).
- **E** migrate recursor-construction field/index recompiles (inductive.clj:298/335), retiring the
  remaining `e/lift`/manual-depth code — highest-risk, do last.

Also pending quick patches: collapse the 3 `parse-binders` + 2 `parse-levels` copies into
`surface/ingest.clj`; add `fun`/`λ` aliases for `lam`; teach `parse-binders` the `:inst` binder.
Full unification deletes ~254 (term.clj) + ~60 (dup helpers) + a slice of `compile-type`'s de-Bruijn
machinery, and leaves ONE elaborator — the foundation for "author wandler like lean-wandler".
