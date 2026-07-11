# The Relational Layer — Design Space & Evidence

Status: living document on the `relational-experiment` branch. This is the
gate for landing `ansatz.rel` (+ provenance, datahike projection) into ansatz
main: the design has to be settled and the value demonstrated, not argued.

## Thesis

Ansatz core stays a conservative, Lean4-faithful kernel + surface. The bet of
the relational layer is one level up: a **mixture-of-provers orchestration
substrate** where every proof-producing mechanism — library recall, instance
synthesis, decision procedures, external ATPs, an LLM — is a *weighted move
generator* over **pure search states**, composed by one driver (`inhabito`),
triaged by **provenance measures** (never assign measure zero; project, don't
sample), and disposed by the **trusted kernel** (`certify` → strict
`check-constant`). Lean has the provers; its monadic tactic framework cannot
offer suspendable, forkable, queryable, re-weightable search state. That
architectural difference — interaction bandwidth with the proof state, for
humans and LLMs — is where a fundamental (≥10×) gain can honestly live.
Search-speed parity alone is not the claim.

## What Lean cannot do (and we can)

- **States as values**: fork/suspend/resume/re-weight a search; a failed
  branch is data (`bestfirst` frontier entries), not an error message.
- **Omnidirectionality**: `inhabito` is one relation — proving, term
  synthesis (`expro`), and sketch completion are presets of the same driver.
- **Measure-carrying conjectures**: the env-overlay admits lemma-holes as
  axioms with tracked provenance; `certify` reports `:assumed`; measures do
  Bayesian triage over which holes to attack (ProbLog semantics, Aesop-shaped
  operationally).
- **Relational recall**: the library as a queryable fact base (disc-tree now;
  datahike for arbitrary conjunctive queries over declarations + proof traces).

## Evidence so far

### E0 — re-find deleted Mathlib proofs (calibration)

50 seeded-random Mathlib theorems (`bench/e0_refind.clj`, seed 42, type-size
≤ 250, compiler-generated aux excluded), proof stripped, statement re-proven
from the library with the theorem itself excluded from recall.

Lean baseline (`bench/e0_lean.lean`, same statements via `type_of%`):

| system | solved | notes |
|---|---|---|
| Lean `aesop` | 20/50 | real white-box baseline (default rule set + simp) |
| Lean `exact?` | 48/50 | self-hit sanity check (finds the theorem itself); 2 elaboration quirks |
| ansatz recall→bestfirst | *pending* | re-running after the disc-tree fix below |

**E0's first yield was system defects, found before any solve-rate number:**

1. **Disc-tree keying bug (fixed, PR #60)**: `expr->keys` had no mvar-head
   case for applications, so mvar-headed apps (the `m β` type argument of
   *every monadic lemma*) keyed as `other` instead of `★` — making the whole
   monadic fragment unreachable for recall and silently degrading simp
   retrieval. Lean parity restored (`DiscrTree.pushArgs`); `List.foldlM_pure`
   goes from unmatchable-with-2795-tied-noise to self-match at score 7.
2. **Unbounded single-defeq confirms (open)**: most recall confirms cost
   10–500ms, but occasional candidates take minutes inside one `is-def-eq`
   call. A confirm that expensive is useless — needs a fuel/depth budget on
   the confirm path (Lean bounds this with `maxHeartbeats`; we have fuel on
   the Java kernel but not on the Clojure-side `applies?` path).
3. **Exception cost on the failure path (fix measured)**: `tc-error!` used
   `ex-info`, whose `elide-top-frames` materializes the full stack per throw;
   inference failures are control flow during search. Direct
   `ExceptionInfo.` construction: ~23% faster failed-confirm loop at
   init-medium scale (125→96ms/200 confirms), larger expected at mathlib
   stack depths.

Method note: this is the loop working as intended — E0 is a *diagnostic that
generates the port list*, classifying every failure into missing-tactic
(port from `../lean4`) vs missing-capability (fix the relational layer),
not just a scoreboard.

### E0, second pass: recall breadth, abortability, and the move-set gap

Three system findings, each fixed or pinned before the solve-rate mattered:

1. **Recall breadth (fixed).** v1 eagerly kernel-confirmed the top-150
   structural candidates per goal, then branched 40-wide — timeout 47/50.
   But the eager confirm is *redundant*: best-first runs `applyo` to expand
   each candidate, which performs the identical unification. Fix:
   `recall-provider` returns a small (12) specificity prefix, unconfirmed;
   `applyo` confirms lazily in measure order. Search now TERMINATES.
2. **Abortability (fixed).** Timeout cases spawned CPU-bound kernel calls
   that survived `future-cancel` and pinned the machine (load 22). The Java
   kernel now polls `Thread.isInterrupted()` in `isDefEqCore`/`whnfCoreImpl`
   (Lean's `check_system`); the harness aborts a runaway node by
   interrupting the worker. Load stays flat; benchmarks are now reliable.
3. **The move-set gap (the real finding).** Clean full E0 with both fixes:
   **3 proved, 27 exhausted, 19 timeout, 1 cert-failed** — vs `aesop` 20/50.
   Classifying the 46 unsolved by conclusion head:

   | count | family | closer it needs |
   |------:|--------|-----------------|
   | 18 | `Eq` | `rfl` / `simp` |
   | 11 | domain-structure (Filter/CategoryTheory/Measure…) | genuinely hard |
   | 7 | `Iff` | constructor / `simp` |
   | 4 | apply-ish | recall + measure |
   | 3 | set/logic | `intro` + unfold |
   | 3 | order/arith | `omega` |

   **~35 of 46 need closing tactics we ALREADY HAVE — `rfl`, `simp`,
   `omega`, `decide`, `intro` — but that were never wired into the
   relational move set** (`{assumption, apply-recalled-lemma}` only). That
   is why aesop (which runs simp+intro+apply+rfl) gets 20 and we get 3. The
   gap is INTEGRATION, not porting: wiring each existing tactic as a weighted
   relational leaf is exactly the mixture-of-provers design. Only ~4 are
   pure recall-ranking targets (where the measure, #2, is the lever) and
   ~11 are hard domain proofs.

   **Consequence for the plan:** the move set must carry the closers before
   the measure (#2) can matter — you cannot rank candidates for an
   `Eq`-by-`rfl` goal that has zero applicable moves.

### E0, third pass: the tactic bridge — 3 → 12 proved

Wired the existing tactics as relational moves. The bridge is a repackaging,
not a translation: the tactic proof-state's `:meta-mctx` IS the rel state's
`:mctx` (both `ansatz.meta`), and a rel goal mvar already carries its
type+lctx there, so `tactico-close` packages the rel goal as a one-goal
proof-state, runs the tactic (`omega`/`decide`/`simp`), and threads the
closed metacontext back. `rflo` closes Eq/Iff/HEq by definitional
reflexivity directly.

Two fixes fell out:
- **`certify` universe bug (load-bearing).** `certify` declared `[]`
  universe params, so EVERY universe-polymorphic goal was rejected as
  `undefined universe level parameter u_N` — silently failing all
  polymorphic closes (they showed as `cert-failed`). `collect-level-params`
  (Lean's `collectLevelParams`) collects them from goal+proof. This alone
  converted 7 cert-failed → proved.
- **simp at Mathlib scale.** The inherited `@[simp]` corpus is ~90k lemmas
  that simp resolves+keys from PSS on EVERY call (~the recall-dump cost per
  simp). `:core-only?` restricts to the 40-lemma hand-curated set as a
  stopgap; a cached SimpTheorems index is the real fix. `simpo`'s bridged
  proof term is also malformed on non-trivial goals — dropped from the move
  set pending a proof-term fix.

Result with the sound closers (`rflo`/`omega`/`decide`) + recall + the
universe fix: **12 proved / 17 exhausted / 18 timeout / 0 cert-failed** —
vs `aesop` 20/50. From 3/50 (15% of aesop) to 12/50 (60%), soundly.

### E0, fourth pass: the persistent @[simp] index

Built the cached full-`@[simp]` index (ansatz.simp-index): dump `name →
LHS-key` once offline (90,328 keys, 3.1MB, ~31 min), load a compact
`key → name` trie at boot (low memory — no 90k CIs in heap), and serve the
inherited corpus LAZILY at simp time (candidate names by the goal-subterm
key, rule resolved+extracted+cached on demand). The 90k-rebuild-per-call
cliff is gone; the trie loads in seconds and interactive proving fits a
modest heap.

E0 with full simp: **13 proved / 10 exhausted / 25 timeout / 2 cert-failed**
— BUT this run was measured under heavy CPU contention (an unrelated app at
load ~17), which inflated timeouts and starved two fast-provers that had
proved in <1 s the run before. Net of the artifact: full simp genuinely
ADDS ~3 simp-closable proofs (Commute.units_inv_left_iff,
Nat.minFac_eq_two_iff, DHashMap…replicate_nil). Two lessons:

1. **cert-failed returns (2):** simp's bridged proof term IS malformed on
   some goals — so `simpo` needs a cheap per-close certify gate (simp closes
   rarely, so gating just its closes is affordable, unlike the all-closer
   gate that stalled the search).
2. **Granularity:** full simp as a per-node LEAF is expensive even with the
   lazy index — simp is a whole simplification traversal, so trying it at
   every search node competes with the time budget. simp likely belongs as
   selective/top-goal preprocessing, not a per-node move.

Remaining gap: fix the 2 cert-failed (gate); apply simp selectively; a clean
(uncontended) re-run for the true number; and the still-untested **measure**
to cut the timeouts (the ProbLog/best-first thesis) + ~11 hard domain proofs.

### Recall projection (B+G) — validated

Persistent disc-key artifact (348,654 useful-decl conclusion keys, ~16MB):
mathlib boot + instance registry + recall trie = ~91s total vs ~13min
re-keying per session. Trie load is ~68s of that — a serialized-trie format
is an easy follow-up win.

## Experiment ladder (agreed)

- **E0** (this doc): calibration vs `aesop`/`exact?` — running.
- **E1** — the load-bearing test: the same LLM (Claude) drives both harnesses
  on held-out problems; ansatz-rel via REPL states/overlays/recall vs Lean
  via LSP. Metric: proofs per wall-clock hour and per token. If the
  interface multiplier isn't large, the thesis is wrong.
- **E2** — external meaning: kernel-certified formalization of a
  recently-solved-informally Erdős problem (elementary, no formal proof
  anywhere), via overlay-conjecture decomposition + measure triage. The
  postmortem must say where the machinery earned its keep vs where the LLM
  did the math.
- **E3** — a query no Lean tool can express: datahike analogy-mining over
  declarations + proof traces that *finds* a proof `exact?`/loogle/leansearch
  structurally cannot.

## Known sharp edges / debts

- `certify` returns `:ok? true` with non-empty `:assumed` (documented; caller
  must check both — consider splitting into `:ok?`/`:fully-proved?`).
- Tactic-arsenal gap vs Lean (`ring`, `linarith`, `norm_num`, `positivity`,
  full `simp` sets): the boring breadth that dominates head-to-heads; port
  from `../lean4` as E0/E1 failures demand, or route through an ATP-as-refiner.
- Datahike module pins an unreleased branch (git-sha; build.clj prep quirk
  documented in deps.edn).
- The `:datatype`/policy-search prototypes on the ansatz side
  (`datatype-core-logic-prototype` branch) overlap this direction and are
  explicitly NOT for merge; reconcile by consuming their good parts (premise
  index as env extension, NDJSON training export) as rel move generators.
