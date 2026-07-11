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
