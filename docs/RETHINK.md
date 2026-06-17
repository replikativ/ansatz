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
