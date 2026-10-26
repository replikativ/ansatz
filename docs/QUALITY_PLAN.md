# Tactic-layer quality plan

Goal: a Lean 4 proof script over user-defined data (recursive functions, structures, lists of
records) behaves in ansatz as it does in Lean. The tactics have Lean's semantics, fail loudly,
and terminate within a budget. The kernel and elaboration of definitions are not the problem
(both are solid); the tactic layer is.

## Where we are (2026-10-26)

Evidence:
- **spindel probe** (`test/ansatz/memory_model_probe_test.clj`): 4 failures, all in tactics.
  - `decide`: a scoped instance had leaked into the Init registry.
  - `induction`: no generalization of dependent hypotheses.
  - `simp_all`: a single round, and a crash on conditional hypotheses that was swallowed.
  - `grind`: an unbounded re-split loop.
- **List conformance** (`test/ansatz/list_conformance_test.clj`, Lean reference
  `test/lean/list_conformance.lean`): 20 standard lemmas over user-defined
  functions, proved with Lean's own scripts translated line by line. Score 5/20 → 20/20 after
  three plumbing fixes: `simp [h]` and `simp [*]` silently dropped hypotheses, and
  `simp … at h` did not exist.
- **Static audit** of `src/ansatz/tactic/`:
  - Only `ac_rfl`, `match_eqns` and the core of `omega` are faithful ports. `grind`, `linarith`,
    `ring`, `norm_num`, `positivity` and `gcongr` are heuristics; the rest are partial ports.
  - 189 broad `catch Exception/Throwable` sites; only 23 catch just tactic errors. A programming
    error therefore turns into "no progress" or a wrong fallback.
  - Silent caps: simp depth 20, Fourier–Motzkin 100 iterations, instance candidates truncated to 32.
  - Name-string hacks where Lean uses structural information or attributes.
  - The surface encoding diverges from Lean: `if` becomes `Bool.rec`/`dite`, and comparisons
    become `Nat.ble`/`Nat.beq` instead of `ite`/`decide`, so Lean's simp set does not apply as-is.

Diagnosis: there is no single broken algorithm. The failures form a pattern of divergence from
Lean plus silent failure, and silent failure is the multiplier: each gap shows up as "made no
progress" far from its cause.

## Yardstick (governs everything below)

Conformance suites are ported from Lean **with Lean's own proofs**, kept in Lean reference files
that `lean_run_code` checks, and scored. A score that drops blocks a merge. Grow the suites to
~150 lemmas:

| Suite | Content | Why |
|---|---|---|
| lists (have 20) | user list functions | baseline |
| records | lists of structures, field projections, alists | spindel model shape |
| bool/decide | Bool algebra, `decide`, `if` on comparisons | the surface encoding |
| nat/int | `omega`, `simp_arith`, induction with arithmetic | everyday lemmas |
| option/prod | `cases`, `rcases`/`obtain`, `match` | pattern-shaped proofs |
| prop-inductive | `Sorted`/`Perm`-like inductive predicates, `cases` on hypotheses | invariants |
| grind | Lean's own grind test cases over user definitions | grind port acceptance |
| spindel | invariant-preservation lemmas over the alist state machine | the next workload |

## Phases

### Phase 0: baseline and guardrails (sequential, coordinator)
- 0.1 Land today's fixes as one PR. This covers: the decide registry, `induction` generalization,
  the `simp_all` fixpoint, conditional hypothesis rewrites, And-projection proofs, `simp [h]`,
  `simp [*]`, `simp … at h`, the grind split budget/timeout, the docs, and the probe and
  conformance tests.
- 0.2 The full suite runs out of memory in one 3 GB JVM (at `prelude.list-test`; every namespace
  passes when run in two JVMs). Either stop retaining per-namespace envs in `delay`s, or run the
  suite in groups.
- 0.3 Worker harness:
  - `scripts/worker.sh TASK` starts `codex exec -m gpt-6.1-sol -c model_reasoning_effort=medium`
    in its own worktree with the task brief, writes the result file, and leaves a branch.
  - A JVM queue (flock on `/tmp/claude-1000/jvm.lock`), so workers wait their turn for test runs
    instead of exhausting memory.
  - `scripts/score.sh` runs the suite plus all conformance suites and prints the scores.

### Phase 1: fail loudly (makes every later phase debuggable)
- 1.1 Exception policy: swallow only `ExceptionInfo` with `:kind :tactic-error` and rethrow the
  rest. Order: grind `try-with-progress`, `simp_all`, the simp congruence/proof builders, the
  instance resolver chain, `all_goals`/`try`/`first`. Expect latent bugs to surface. Each one is
  fixed or written up in `docs/quality/revealed.md`; none is re-hidden.
- 1.2 Silent caps become errors, or are removed where Lean has no such cap (simp depth 20 → rely
  on maxSteps).
- 1.3 Tactic-language semantics:
  - `all_goals`/`and_then` rethrow like `evalAllGoals`.
  - Unknown lemma or hypothesis names are errors.
  - One newest-wins name lookup everywhere.
  - Lean's `induction … with | cons h t ih`, plus `case`/`next`.
  - Locations `at h ⊢` for `simp`, `rw` and `simp_all`.
  - `intro`/`intros` give anonymous binders inaccessible names as Lean does (`a✝`).

### Phase 2: faithful cores (parallel tracks)
- **A. grind**: port Lean's architecture (Meta/Tactic/Grind) around the existing E-graph and
  E-matching: preprocess → internalize → propagate → E-match rounds with generations → split
  with the `splits` budget, refutation-based. Acceptance is the grind suite.
  *Decision: port it, or run Lean's own grind through the Lean interpreter on our kernel (see below).*
- **B. Instance synthesis**: Lean's tabled `SynthInstance` with DiscrTree keys and priority
  order; delete the name-based fallbacks.
- **C. simp**: `Simp.Config` defaults (`decide := false`), `simp_arith`, and `simp_all` with
  Lean's replace-and-clear (unblocked by D).
- **D. Surface encoding**: elaborate `if` to `ite`/`dite` with a synthesized `Decidable`
  instance, and comparisons to `decide`, keeping the fast runtime lowering (`@[csimp]`-style
  mapping in codegen). This removes the `Nat.ble`/`Bool.rec` special cases in simp, `simp_all`
  and grind. *Decision: it is a breaking change for wandler/codegen.*
- **E.** `ring`/`linarith`/`positivity`/`norm_num`: real certificates. Lower priority for spindel.

### Phase 3: deduplication, cleanup, test consolidation
- Remove the name-string hacks: matchers via MatcherInfo; equation lemmas under Lean's names
  (`f.eq_N`, `f.eq_def`); instance discovery by attribute, not substrings.
- Consolidate tests: one namespace per tactic, the conformance suites as the primary acceptance
  layer, delete duplicated or obsolete scripts, shared env fixtures (also fixes 0.2).
- Update CLAUDE.md and the README to match.

## Coordination model
- **Coordinator** (Claude, this session): writes the briefs (`docs/quality/tasks/Txx.md`: goal,
  Lean files to port from, scope fence, acceptance), dispatches workers, merges sequentially, runs
  the scores, keeps this plan current.
- **Workers**: `codex exec`, gpt-6.1-sol, medium effort; one task per worktree and branch.
- **Reviewers**: a second Codex run (`codex exec review`) or a Claude agent per diff. The review
  is against the Lean source, not the worker's summary.
- **Merge gate**: suite green; no conformance score drops; no new broad catch.
- **Constraint**: about 4–5 GB of free RAM means one JVM at a time. Workers can read, write and
  review in parallel; JVM test runs queue. Throughput is bounded by test time, not by the number
  of workers.
