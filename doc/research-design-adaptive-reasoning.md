# Adaptive Reasoning over Towers of Abstraction

## A Research Design for Integrated Formal, Symbolic, and Numerical Reasoning

*Christian Weilbach, March 2026*

---

## 1. Core Thesis

All cognition — biological, artificial, formal — is **search over structured
representations**, where the efficiency of search depends on:

1. **Identity recognition**: detecting when two states are equivalent (hash-consing, memoization, caching)
2. **Perspective selection**: choosing which level of abstraction to reason at (abstract interpretation, coarse-graining, delegation)
3. **Budget allocation**: distributing finite computational resources across competing search branches (importance sampling, MCTS, adaptive scheduling)

These three concerns compose into a **self-improving system** when the search
process itself is observable, forkable, and persistent — enabling learning over
search strategies, not just search outcomes.

## 2. Empirical Grounding: Lessons from Lean 4 Kernel Verification

### 2.1 The Hash-Consing Lesson

We implemented a complete Ansatz (Calculus of Inductive Constructions) type checker
in Java, verified against Lean 4's kernel on all 648,612 Mathlib declarations
(91M expressions). The key finding:

- **Without hash-consing**: exponential blowup on algebraic proofs (>30s timeout on `SubfieldClass.toField`)
- **With hash-consing**: 6ms for the same declaration, 99.993% of Mathlib verified in 29 minutes

Lean 4's kernel resolves 64% of definitional equality checks via **pointer
equality** — recognizing that two terms are literally the same object in memory.
Our checker initially achieved only 7%. The fix was a thread-local intern table
that deduplicates all expressions created during type checking.

**Generalized principle**: In any term-rewriting system (type checker, CAS,
compiler optimizer, abstract interpreter), the dominant cost is redundant
comparison of structurally identical terms. Identity management is not an
optimization — it is the mechanism that makes search tractable.

### 2.2 The Strategy Schedule Lesson

Lean's kernel isDefEq implements a **fixed priority ordering** of strategies:

```
quick (pointer eq) → proof_irrel → lazy_delta → whnf → eta → structural
```

This ordering encodes a deep heuristic: try cheap identity checks before
expensive reductions. The `lazy_delta` strategy makes a critical choice: when
comparing two constants, unfold the one with **lower reducibility** first.
Human-annotated `@[reducible]`/`@[irreducible]` attributes guide this.

**Generalized principle**: The kernel doesn't search — it checks. But within
checking, there are implicit search decisions (which constant to unfold, which
direction to reduce). The efficiency of the checker depends on these decisions
being well-calibrated to the domain. In general systems, this calibration should
be learned, not hardcoded.

### 2.3 The No-Fuel Lesson

Lean's kernel runs with **no fuel limit** (`maxHeartbeats = 0` during replay).
It relies on termination being guaranteed by the type theory itself. Our 46
remaining failures are fuel exhaustion at 20M steps — the kernel is doing correct
work, just more of it than our budget allows.

**Generalized principle**: When the underlying theory guarantees termination, the
search budget should be unlimited (or very generous). Budget limits are for
*heuristic* search, not *decidable* checking. Know which regime you're in.

## 3. Architecture: The Language DAG

### 3.1 The Levels

The system is organized as a **DAG of reasoning engines** (not a strict tower),
each providing a different precision/cost/expressiveness tradeoff:

```
Level 6: Agent/LLM      (linguistic, heuristic, highest flexibility)
Level 5: Lean/Ansatz       (dependent types, full formal precision)
Level 4: SMT/Datalog    (decidable fragments, automated)
Level 3: CAS/Symbolic   (algebraic manipulation, rewriting)
Level 2: Romeo/IR       (typed numerical computation, nanopass)
Level 1: Hardware        (JAX/Mojo/Futhark execution)
Level 0: SAT/Boolean     (propositional logic, DPLL/CDCL, the bottom)
```

SAT/Boolean logic is the bottom level of interpretation — every decidable
problem can be reduced to SAT, and SAT solvers are the most mature automated
reasoning engines. Z3's SMT solving is layered on top of its SAT core (DPLL(T)).
Making SAT/SMT a first-class level with persistent, forkable state (rather than
a stateless oracle) is critical for incremental reasoning.

Each level has:
- A **term language** with hash-consed identity
- A **reduction relation** (deterministic or weighted/nondeterministic)
- A **trace format** recording which reductions were applied
- **Galois connections** to other levels (abstraction α, concretization γ)
- A **metaprogramming interface** for reflection and code generation

The DAG structure means any level can delegate to any other — Lean can call SMT
(skipping CAS), the LLM can emit Ansatz terms directly (skipping SMT), the CAS can
invoke numerical computation (skipping Romeo IR). The connections are not
restricted to adjacent levels.

### 3.2 Concrete Language Capabilities

Each level is implemented by one or more concrete systems, each with distinct
strengths:

| Level | System | Types | Effects | Metaprogramming | Strengths |
|-------|--------|-------|---------|-----------------|-----------|
| 5 | **Lean 4/Ansatz** | Dependent, inductive | Pure only | `MetaM` monad: type-aware elaboration | Mathlib (1M lines formalized math), industrial tooling |
| 5 | **Agda/Cubical** | Dependent, HoTT | Pure only | `TC` monad: cubical path construction | Univalence, quotients, higher inductive types |
| 4 | **F*/Z3** | Refinement + effects | Tracked (ST, IO, Div) | `Meta` effect: SMT-aware tactics | Verified stateful programs (TLS, crypto, consensus) |
| 4 | **Datalog/datahike** | Relational | Bottom-up saturation | Rule synthesis | Fixed-point computation, reachability |
| 3 | **CAS** | Algebraic | Rewriting | Rule-based | Symbolic simplification, integration |
| 0 | **SAT/DPLL** | Propositional | Deterministic | Clause learning (CDCL) | Universal decidable bottom, forkable state |
| ∞ | **Racket** | Gradual/contracts | Unrestricted | Hygenic macros, phases, `#lang` | Language-oriented programming, macro composition |
| ∞ | **Clojure** | Dynamic | Unrestricted | `defmacro`, runtime `eval` | REPL, orchestration, data transformation, JVM ecosystem |

Racket and Clojure are "meta-levels" that can host any of the others. The
distinction: Racket provides the best **compositional macro system** (hygiene,
phases, module-aware expansion). Clojure provides the best **runtime
orchestration** (REPL, persistent data, JVM interop, unrestricted effects).

### 3.3 Perspective Changes as Fibrations

The levels are not a strict hierarchy. Any reasoner can delegate to any other.
This is modeled as a **fibration** of reasoning categories over a base category
of **perspectives**:

- Moving along the fiber = changing perspective (e.g., from formal proof to numerical simulation)
- The Galois connections = how to translate results between fibers
- An **information projection** = projecting a problem into a cheaper representation to get a noisy signal, then projecting back

Example workflow:
```
Goal: prove convergence of a PDE discretization scheme
  → Perspective change to Romeo/numerical: run coarse simulation, observe convergence
  → Perspective change to CAS/symbolic: find closed-form error bound
  → Back to Lean/Ansatz: formalize the bound using mathlib's analysis library
  → Delegate to SMT: discharge arithmetic side conditions
```

### 3.4 The Category of Measures

During search, the system maintains **weighted distributions** over possible
next steps. This is formalized as the **category of measures** (or more
precisely, the Kleisli category of the probability monad):

- Objects: typed holes (goal + context at some level of the tower)
- Morphisms: weighted tactic/reduction applications
- Composition: sequential application with weight multiplication
- The monoidal structure: parallel/branching search

This subsumes:
- Deterministic checking (point measures / Dirac deltas)
- Nondeterministic search (uniform distributions over applicable tactics)
- Learned search (trained distributions conditioned on goal features)
- Probabilistic programming (the full generality of importance sampling)

## 4. Infrastructure: Forkable Persistent Search

### 4.1 Partial-CPS for Continuation Capture

The `partial-cps` library provides **breakpoint-based continuation capture**:
at designated points in a computation, the "rest of the computation" is reified
as a first-class value. This enables:

- **Forking**: run the same future with different choices
- **Snapshotting**: persist a search state for later resumption
- **Delegation**: send a continuation to a different reasoner
- **Resampling**: discard unpromising continuations, duplicate promising ones

The partial (not full) CPS transform is critical: synchronous code sections
(the vast majority) run at full speed without transformation overhead. Only
breakpoints — the decision points where search branches — incur CPS overhead.

### 4.2 Git-like Branching via Yggdrasil

Yggdrasil's copy-on-write protocol stack provides the **version control
semantics** for search:

- **Branch**: speculative exploration of a search direction
- **Commit**: checkpoint a search state (goal + partial proof + context)
- **Merge**: combine results from compatible search branches
- **Rebase**: replay one strategy's steps in a different context
- **GC**: discard abandoned search branches

This operates across heterogeneous storage: the proof state (datahike), the
expression arena (FlatStore/mmap), the trace log (scriptum), the learned
strategy weights (proximum for embedding-based retrieval), and solver states
(Z3/SAT constraint sets) all branch and merge together. The key principle:
**every reasoning engine must have forkable state**, not just a stateless query
interface. A stateless oracle can only be called; a forkable state can be
navigated, checkpointed, and explored like a search tree.

### 4.3 Sequential Monte Carlo over Reasoning Traces

The combination of partial-CPS + yggdrasil branching implements **SMC
(particle filtering) over computation traces**:

- **Particles** = active search branches (forked continuations)
- **Importance weights** = heuristic assessment of branch promise
- **Resampling** = discard low-weight branches, duplicate high-weight ones
- **Proposal distribution** = the strategy selector (LLM, learned model, or hardcoded heuristic)
- **Observations** = intermediate results (subgoal closed, simulation converged, SMT returned SAT)

Each `observe` (in the probabilistic programming sense) is a **breakpoint**
where the orchestrator reassesses. The key insight from probabilistic
programming (Anglican/Daphne): the quality of inference depends primarily on the
**proposal distribution**, not the number of particles. Learning good proposals
from accumulated traces is where the system self-improves.

## 5. Staged Metaprogramming across the Language DAG

### 5.1 The Core Problem: Interleaving Elaboration with Computation

Formal reasoning requires **interleaving** type-theoretic elaboration with
computational effects at different levels. Consider proving convergence of a
numerical method:

1. Run a coarse numerical simulation to estimate the convergence rate (Level 0-1)
2. Use a CAS to derive a closed-form error bound from the estimate (Level 2)
3. Discharge the bound's arithmetic constraints via SMT (Level 3)
4. Construct the formal proof in Ansatz using the bound (Level 4)

This cannot be a pipeline — step 4 may generate new subgoals that require
returning to steps 1-3. The computation must **suspend** at one level, **drop
down** to another for results, and **resume** with those results.

### 5.2 The `stage` Form: Cross-Level Computation

We introduce a `stage` form that marks transitions between reasoning levels
within an elaboration context:

```clojure
(elaborate env
  (theorem convergence [ε : Real, hε : (> ε 0)]
    (let [n-estimate (stage :numerical
                       (find-n-for-convergence f ε 1e-12))]
      (let [bound (stage :cas
                    (simplify (error-bound f n-estimate)))]
        (have h1 : (≤ (error-bound f n-estimate) ε)
          (stage :smt (z3-check (≤ bound ε))))
        (apply error-bound-implies-convergence h1)))))
```

**Mechanism**: `stage` is implemented via **partial-CPS**. At each `stage`
boundary, the current elaboration continuation is captured. The inner
computation runs at the target level (numerical, CAS, SMT). Its result is
injected back into the captured continuation, which resumes elaboration.

This is not speculative — partial-CPS already provides exactly this capability.
The `stage` form is syntactic sugar over `breakpoint` + `resume`.

### 5.3 Three Kinds of Metaprogramming

Metaprogramming in our system operates at three distinct levels, which nest
and compose freely:

**Kind 1: Syntax-level (Clojure macros)**

Classic `defmacro` — transforms s-expressions at read/compile time. Sees only
syntax, no types. Useful for surface sugar (`theorem`, `deflean`, `by` blocks).

```clojure
(defmacro theorem [name binders type & body]
  `(let [goal# (elaborate ~'env (quote (forall ~binders ~type)))]
     ...))
```

**Kind 2: Type-directed (elaborate + kernel)**

Runtime functions that call `infer-type`, `is-def-eq`, `whnf` to make decisions
based on types. This is what Lean's `MetaM` provides. We now have this via
`elaborate` + the tactic layer.

```clojure
(defn auto-step [env ps]
  (let [goal-type (whnf (goal-type ps))]
    (cond (forall? goal-type) (intro ps)
          (eq-head? goal-type) (try-rfl ps)
          :else (suggest-tactic env ps))))
```

**Kind 3: Cross-level staging**

Suspend computation at one level, execute at another, resume with the result.
Implemented via partial-CPS continuation capture.

```clojure
(elaborate env
  (theorem ... (let [n (stage :smt (check-bound ε))] ...)))
```

**The key insight: these compose freely.** Kind 2 subsumes Kind 1 in our system
because Clojure macros run at "runtime" in the REPL — `macroexpand` is a
function, `eval` is always available, the phase distinction dissolves. A macro
can call `elaborate` at expansion time, and `elaborate` can internally stage.
This is deliberately less disciplined than Racket's phase separation because
**adaptive reasoning requires deciding at runtime which level to stage into**.

The safety net is the kernel: no matter how the staging dances, the final term
must type-check.

### 5.4 Metaprogramming at Each Level

Each level in the DAG has its own notion of metaprogramming:

| Level | Metaprogramming | Access to types? | Hygiene? |
|-------|----------------|-------------------|----------|
| **Lean 4** | `MetaM` monad | Full (elaboration-aware) | Scoped names |
| **Agda** | `TC` monad | Full (cubical path-aware) | Module-scoped |
| **F*** | `Meta` effect | Refinement-aware | Effect-tracked |
| **Z3/SAT** | Tactic scripts, `push`/`pop` | Solver state | N/A |
| **Racket** | Phase-separated macros | Syntax only (per phase) | Hygienic |
| **Clojure** | `defmacro` + runtime `eval` | None (syntax only) | Manual |

**ansatz makes Clojure's metaprogramming type-aware**: the Ansatz kernel is a
Clojure library, so macros and runtime functions can call `infer-type`,
`is-def-eq`, and `whnf` during expansion. This gives Clojure macros capabilities
closer to Lean's `MetaM` than to traditional Lisp macros.

### 5.5 First-Class Elaboration (Operational)

The `elaborate` function (`ansatz.surface.elaborate`) is a **runtime function**
(not a macro) that performs:

1. **Name resolution**: look up identifiers in the environment
2. **Implicit argument insertion**: create metavariables for implicit/instance
   args, solve them via first-order unification
3. **Universe level inference**: create level metavariables, solve from type
   constraints
4. **`@`-prefix for explicit mode**: suppress implicit insertion (like Lean's `@`)
5. **Zonking**: substitute all solved metavariables in the final term
6. **Verification**: optionally verify the result through the kernel type checker

This is strictly more powerful than a macro because it has access to the full
environment and type checker at call time. It can be called inside proof search
loops, inside `stage` forms, and from the REPL.

### 5.6 Proof Preservation across the Stack

When staging results between levels, three regimes apply:

**Regime 1: Sound lowering (proof-preserving Galois connection)**

The translation itself preserves proofs. Example: lowering a Ansatz proposition to
SMT. If Z3 returns `UNSAT` for the negation, that's a valid proof witness.
F* does this — the `smt()` tactic translates a VC to SMT-LIB, Z3 returns
`UNSAT`, F* trusts this as a proof. We can reconstruct Ansatz proof terms from
Z3's proof certificates, or trust the oracle axiomatically.

**Regime 2: Proposals from lower levels (weaken then re-verify)**

Lower levels provide *witnesses* or *hints*, not proofs. The higher level must
verify. This is the most common and most useful pattern:

```
Ansatz: prove ∃ n, error(f, n) < ε
  ↓ stage to numerical: run simulation → n=100 works
  ↑ return proposal: try n=100
Ansatz: now prove error(f, 100) < ε    (concrete, easier)
  ↓ stage to CAS: simplify → 0.00297
  ↑ return bound
Ansatz: prove 0.00297 < ε via norm_num or smt
```

The lower level turns an existential *search* problem into a *verification*
problem — exponentially easier. In SMC terms, lower levels are **proposal
distributions**: a good proposal (accurate simulation) means most proposals
are accepted; a coarse one means many are rejected, but any accepted result
is fully verified.

**Regime 3: Proof transport (cubical path types, future)**

When composing results across levels that use structurally different encodings,
we need to prove the translation preserves meaning. In Ansatz this requires
explicit equivalence proofs. In cubical Agda, transport along paths is
computational — not a proof obligation. This matters for:
- Composing staging pipelines without re-checking at each step
- Transferring proofs between different inductive encodings
- Quotient types (where Ansatz requires setoid reasoning but cubical Agda
  has proper quotients via higher inductive types)

Near-term, Regime 2 (propose/verify) handles most cases. Path types become
important for *compositional* staging guarantees.

### 5.7 Forkable Solver State

A critical architectural decision: reasoning engines at every level must have
**persistent, forkable state**, not just stateless query interfaces. This
applies to:

- **Ansatz proof states**: already forkable (immutable Clojure maps)
- **Z3/SAT state**: being ported with persistent push/pop/fork semantics, so
  constraint sets can branch and merge like git branches
- **CAS state**: rewrite rule sets and assumption contexts, forkable
- **Numerical state**: simulation checkpoints, resumable

Standard Z3 has a linear `push`/`pop` stack. Forkable Z3 means you can:
- Branch a constraint set, try two assertions, backtrack to the fork point
- Pause Z3 after asserting some constraints, stage up to Ansatz for guidance,
  then resume with additional constraints
- Run parallel Z3 branches with different heuristic configurations

This turns every level from a black-box oracle into a **navigable node in the
DAG** with the same version-control semantics as the proof state (§4.2).
The partial-CPS story applies: a solver state is a continuation.

### 5.8 Surface Syntax and Bidirectional Mapping

Three concrete tools implement the surface layer (all operational):

- **`ansatz/term`** (`ansatz.surface.term`): Named term builder that eliminates de
  Bruijn index pain. `(term env (forall [a Nat] (Eq.{1} Nat a a)))` → Ansatz Expr.
- **`ansatz/pp`** (`ansatz.surface.pp`): Pretty-printer producing readable Lean-like
  syntax from Ansatz exprs.
- **`ansatz/emit-lean`** (`ansatz.surface.lean`): Lean 4 syntax emitter for
  round-tripping terms back to Lean for cross-validation.

### 5.9 REPL-Driven Proof Interaction (Operational)

The tactic layer is implemented and working:

```clojure
(require '[ansatz.tactic.repl :as r])

;; Start a proof
(def ps (r/prove env goal-type))

;; Apply tactics (returns new ps — old ps still available)
(def ps2 (-> ps (r/intro "a") (r/intro "h") r/assumption))

;; Fork is free (immutable data)
(def branch-a (r/rfl ps2))
(def branch-b (r/apply-tac ps2 some-lemma))

;; Verify through Java TypeChecker
(r/qed ps2)

;; LLM-guided search
(def config (r/llm-config))
(r/llm-auto config ps 3 20)
```

Implemented tactics: `intro`, `intros`, `exact`, `assumption`, `apply`, `rfl`,
`constructor`, `rewrite`, `cases`. All produce proof terms verified by the Java
kernel TypeChecker end-to-end.

### 5.10 Match Expression Compilation (Operational)

The `ansatz.surface.match` module compiles surface pattern-matching expressions into
Ansatz recursor applications — the only elimination form the kernel understands.

**Surface syntax**:
```clojure
(match n
  [0             base-case]
  [(Nat.succ k)  (step k)])
```

**Compilation pipeline**:

1. **Parse**: surface patterns → structured `{:tag :ctor/:var/:wildcard/:lit-nat}`
2. **Desugar Nat literals**: `0` → `Nat.zero`, `3` → `Nat.succ (Nat.succ (Nat.succ Nat.zero))`
3. **Look up recursor**: infer the discriminant's inductive type, find `Ind.rec`
4. **Build minor premises**: for each constructor in the recursor's rule list,
   find matching alternatives, build a lambda abstracting over the constructor's
   fields (and IH arguments for recursive fields)
5. **Handle nested patterns**: when a constructor's sub-patterns are themselves
   constructor patterns, recursively compile an inner match on the relevant field
   — a simple form of decision tree compilation
6. **Assemble**: `@Ind.rec motive minor1 ... minorN indices discr`

The motive is non-dependent (`λ (x : IndType) => RetType`). Dependent motives
are not yet needed but follow the same structure with the motive lambda binding
the discriminant.

Nested pattern compilation avoids the full complexity of a general decision tree
or backtracking automaton. The current strategy: find the first field with a
nested constructor pattern, compile a match on that field, threading all
alternatives that overlap on that constructor. This suffices for the patterns
that arise in practice (Nat recursion, Option/List destructuring, Bool case
splits) without requiring exhaustiveness or redundancy checking.

### 5.11 `theorem` and `define` Macros (Operational)

The `ansatz.tactic.repl` module provides `theorem` and `define` — convenience
functions that orchestrate the full definition pipeline:

```clojure
(r/theorem env 'my_thm '(forall [a Nat] (Eq a a))
  (fn [ps] (-> ps (r/intro "a") r/rfl)))
;; => updated env with my_thm added
```

**Pipeline** (`theorem`):

1. **Elaborate type**: `(elab/elaborate env type-sexpr)` — resolve names, insert
   implicits, infer universe levels
2. **Open proof**: `(prove env type-expr)` — create initial proof state with the
   elaborated type as the goal
3. **Apply tactics**: call the user-supplied `tactic-fn` to transform the proof
   state until all goals are closed
4. **Extract and verify**: `(extract/verify ps)` — extract the proof term from
   the closed proof state and verify it through the Java TypeChecker
5. **Register**: `(env/add-constant env (mk-thm name [] type term))` — add the
   verified theorem to the environment as a new constant

`define` follows the same shape but elaborates a value expression instead of
running tactics, wrapping the result as a definition with reducibility hints.

The key property: no term enters the environment without passing through the
kernel type checker. The macros are orchestration sugar; soundness rests entirely
on the kernel's `add-constant` + type checking.

### 5.12 Flexible Functorial Compilation

The DAG architecture (§3.1) implies that compilation between levels should not
be a single fixed pipeline but a **dynamic choice of translation paths**. A
proof obligation at Level 5 (Ansatz) might be discharged by:

- Lowering to SMT (Level 4) if it falls in a decidable fragment
- Staging to numerical simulation (Level 1) for a witness, then verifying
- Staying within Ansatz and applying tactic automation
- Asking an LLM (Level 6) for a proof sketch, then elaborating and checking

Each path is a **functor** between the reasoning categories at two levels,
preserving the relevant structure (types, reduction, identity). The
orchestrator's job is to select the functor at runtime based on:

- **Goal structure**: is the head symbol arithmetic? propositional? algebraic?
- **Available engines**: which solvers/levels are currently instantiated?
- **Budget**: how much compute remains? cheap paths first
- **Learned weights**: historical success rates for similar goals

This is not yet implemented as a general framework, but the pieces exist: the
`stage` form (§5.2) provides the suspension/resumption mechanism, the `elaborate`
function provides type-directed dispatch, and the tactic layer provides the
within-Ansatz automation. The missing piece is a **routing policy** that examines a
goal and selects a translation path — initially rule-based, eventually learned
from accumulated traces (§4.3).

### 5.13 Advanced Tactic Agenda

The current tactic set (`intro`, `apply`, `rfl`, `rewrite`, `cases`, etc.)
handles structural reasoning. Three families of **computational tactics** are
planned for later phases:

- **`simp`** (simplification): congruence closure + a set of rewrite lemmas
  applied to saturation. Requires maintaining a `simp` lemma database (tagged
  declarations in the environment) and an e-matching loop. The forkable state
  design (§5.7) means the lemma set itself can branch — different proof branches
  can carry different `simp` configurations.

- **`ring`** (ring solver): normalize ring expressions to a canonical polynomial
  form via reflection. The standard approach: quote the goal into an abstract
  polynomial AST, normalize via verified Horner form, compare. This is a natural
  candidate for the CAS level (Level 3) — the normalization is symbolic algebra,
  and the correctness proof can be either carried out in Ansatz or trusted as an
  oracle with a verified reflection lemma.

- **`omega`** (linear arithmetic over Nat/Int): a decision procedure for
  quantifier-free linear arithmetic. Can be implemented as a Ansatz tactic
  (reflection-based, like Lean's `omega`) or delegated to SMT (Level 4) via
  the planned Ansatz→SMT-LIB translation. The SMT path is simpler to implement;
  the reflection path produces smaller, self-contained proof terms.

These three tactics cover the majority of "boring" proof obligations in
formalized mathematics. Their implementation will follow the same pattern as
existing tactics: produce a Ansatz proof term, verify through the kernel, never
trust the tactic itself.

## 6. Formalization in Lean

### 6.1 What to Formalize First

We propose formalizing the following concepts in Lean/Mathlib, both as a
validation of the framework and as executable specifications:

1. **Galois connections between term algebras**: formalize the abstraction/
   concretization maps between levels of the tower. Mathlib already has
   `GaloisConnection` and `GaloisInsertion`.

2. **The category of weighted relations** (Kleisli category of the distribution
   monad): this gives the categorical semantics of our search process. Define
   morphisms as `A → Measure B` with composition via integration.

3. **Fibered categories for perspective changes**: formalize the fibration
   structure where the base category is "perspectives" and fibers are reasoning
   categories at each perspective.

4. **Abstract interpretation soundness**: given a Galois connection `(α, γ)`
   between a concrete and abstract domain, prove that abstract execution
   over-approximates concrete execution. This is the correctness criterion for
   the tower.

### 6.2 Lean as a Level in Its Own Tower

A key reflexive property: Lean itself is one level in the tower it formalizes.
The formalization of Galois connections *in Lean* is verified *by Lean's kernel*,
which is itself an instance of the pattern being formalized. This reflexivity
is a feature: it means the system can reason about its own reasoning process.

The ansatz kernel checker makes this concrete — we have an independent
implementation of Ansatz that can verify Lean's own proofs about Ansatz. The tower
of interpreters is not just a metaphor; it is literally implemented as
interoperating verification engines.

### 6.3 SMT and Beyond

Where Lean's automation falls short, we can integrate:

- **SMT (Z3/CVC5)**: for decidable fragments (linear arithmetic, bitvectors,
  arrays). F*-style refinement types translate VCs to SMT queries.
- **E-graphs (egg)**: for equality saturation in compiler optimization passes.
  Rather than choosing rewrite direction (source of exponential blowup), explore
  all equalities simultaneously.
- **Datalog (datahike)**: for bottom-up saturation of relational facts. The
  semi-naive evaluation strategy is essentially equality saturation for
  relational data.

Each of these is a **specialized search engine** for a specific fragment. The
orchestrator's job is to recognize which fragment a subgoal belongs to and
delegate accordingly.

## 7. Implementation Plan

### Phase 1: Interactive Ansatz from Clojure REPL ✓

**Status**: Complete. ansatz kernel checker at 99.993% Mathlib pass rate.

- [x] Proof state data structure: goals, metavar context, partial term extraction
- [x] Basic tactics: intro, intros, exact, assumption, apply, rfl, constructor, rewrite, cases
- [x] Proof term extraction with end-to-end Java TypeChecker verification
- [x] Surface syntax: `ansatz/term` (named term builder), `ansatz/pp` (pretty-printer), `ansatz/emit-lean` (Lean 4 emitter)
- [x] REPL integration (`ansatz.tactic.repl`)
- [x] Beam search over tactic space (`ansatz.tactic.search`)
- [ ] Remove fuel limit, rely on per-declaration timeout (matching Lean behavior)

### Phase 2: LLM-Guided Proof Search (In Progress)

- [x] NDJSON trace export format for proof search (`ansatz.tactic.trace`)
- [x] LLM client for Fireworks/OpenAI-compatible APIs (`ansatz.tactic.llm`)
- [x] LLM tactic suggestion with response parsing (`ansatz.tactic.suggest`)
- [x] LLM-guided beam search with fallback to enumerate-tactics
- [x] **`elaborate` function**: runtime elaboration with name resolution, implicit argument insertion, universe level inference, `@`-explicit mode, zonking, and kernel verification (`ansatz.surface.elaborate`)
- [x] **Instance resolution for `Decidable`**: search env for typeclass instances, assemble fully-applied instance terms via recursive unification
- [x] **`decide` tactic**: build `@of_decide_eq_true P inst rfl`, kernel evaluates decision procedure
- [x] **Ansatz→SMT-LIB translation**: lower decidable Nat/Int arithmetic fragment to SMT-LIB
- [x] **Mock Z3 + `smt` tactic**: mock solver for prototyping, trust axiom fallback
- [x] **`theorem`/`define` macros**: REPL convenience for defining theorems and definitions (`ansatz.tactic.repl`)
- [x] **`simp` tactic**: bottom-up rewriting with lemma index, traversal under binders, `dsimp`, `simp only [...]`
- [x] **`ring` tactic**: sparse polynomial normalization with grevlex ordering, certifies via `decide`/`rfl`
- [x] **`omega` tactic**: ground Fourier-Motzkin linear arithmetic, certifies via `decide`
- [x] **`omega-proof` tactic**: full non-ground omega with proof term construction — auto forall intro, by_contra, implication/Iff decomposition, div bounds, mod decomposition, Neg.neg handling, Nat.sub dichotomy, hard equalities via bmod, divisibility
- [x] **Match expression compilation**: surface patterns → Ansatz recursor applications, nested patterns, Nat literal desugaring
- [ ] Integrate partial-cps breakpoints into proof search
- [ ] Connect proof state branching to yggdrasil for persistence
- [ ] Implement SMC resampling over proof branches

### Phase 3: Forkable SAT/SMT Integration (Complete)

- [x] Forkable SAT/SMT state: persistent/transient/fork semantics with <1ms deep copy (zustand/sat-clj)
- [x] CDCL SAT solver competitive with Z3 (~195ms vs ~330ms on random-200)
- [x] DPLL(T) SMT layer with 11 theory solvers (EUF, Arith/Simplex, Arrays, BV, FP, Datatypes, Quantifiers, Strings, DiffLogic, PB, Sets)
- [x] Clojure data-oriented API (`zustand.smt`) with expression data ↔ Java Expr conversion
- [x] MaxSMT (core-guided Fu-Malik) for optimization
- [x] MILP support with pseudocost branching, Gomory cuts, MIR cuts
- [x] Intercept callbacks at RESTART/BUDGET_EXHAUSTED/FINAL_CHECK with persistent snapshots
- [x] Replace mock Z3 with real forkable zustand SMT solver in ansatz `smt` tactic
- [ ] Proof reconstruction: SMT conflict explanations → Ansatz proof terms
- [ ] Simplex state exposure via Clojure API (dual values, tableau, reduced costs)
- [ ] F*-style refinement types for program verification (Paxos/konserve)

### Phase 4: Systems Verification

- [ ] Verified stateful programs: Paxos/Raft consensus, konserve storage
- [ ] Datalog integration for relational reasoning and reachability
- [ ] Effect tracking: encode I/O, state, divergence in the type system

### Phase 5: Staged Cross-Level Computation

- [ ] The `stage` form via partial-CPS for cross-level computation
- [ ] Numerical simulation as heuristic oracle (Romeo → weight for proof branches)
- [ ] CAS/symbolic intermediate layer
- [ ] Nanopass stages as formalized Galois connections
- [ ] Agda/cubical integration for proof transport (path types)

### Phase 6: Self-Improvement Loop

- [ ] Accumulate proof search traces in datahike
- [ ] Learn strategy distributions from traces (goal features → tactic weights)
- [ ] Adaptive budget allocation (more compute for harder goals)
- [ ] Integrate with dvergr agent framework for persistent proof-search agents

## 8. Related Work and Distinctions

| System | Relation to this work |
|--------|----------------------|
| **Lean 4 / Mathlib** | Our verification backend; we extend it with programmable search |
| **F* / Liquid Haskell** | SMT-based refinement types; we integrate SMT as one level, not the only one |
| **Agda / Cubical** | Stronger type theory (HoTT); potential Level 4 alternative for univalence |
| **Racket** | Gold standard for compositional metaprogramming; informs our `stage` design |
| **AlphaProof / HTPS** | MCTS over proof search; we generalize to SMC over heterogeneous reasoning |
| **egg / Metatheory.jl** | E-graph equality saturation; a specific search strategy we can deploy |
| **Anglican / Gen.jl** | Probabilistic programming; provides the theoretical framework for our search |
| **Coq / MetaCoq** | Self-verified kernel; our ansatz serves a similar role for Lean |
| **Isabelle / Sledgehammer** | Multi-prover integration; closest to our multi-engine orchestration |
| **Turnstile+** | Typed macros in Racket; shows how to make macro expansion type-aware |
| **Idris 2 / Elaborator Reflection** | Exposes elaboration as a first-class effect; closest to our `elaborate` |

### Key distinction

Most systems pick one level of the DAG and optimize within it. Our contribution
is the **orchestration layer** — treating the DAG itself as a first-class object
that can be navigated, branched, and learned over. The combination of:

- **Persistent versioned state** (yggdrasil) for branching search
- **Forkable continuations** (partial-cps) for cross-level staging
- **First-class elaboration** (type checker as a runtime function, not a build step)
- **Heterogeneous reasoning engines** connected by Galois connections

is, to our knowledge, novel. The closest existing work is Isabelle's
Sledgehammer (multi-prover), but it treats external provers as black boxes.
We treat the connections between levels as **typed, traceable, learnable**
morphisms in a category of reasoning strategies.

## 9. Open Questions

1. ~~**Forkable solver state semantics.**~~ **Answered**: zustand implements persistent/transient/fork semantics with <1ms deep copy, CDCL SAT competitive with Z3, and DPLL(T) SMT with 11 theory solvers. The abstraction is persistent data structures with copy-on-write internals — the same pattern as Clojure's persistent collections, applied to solver state. Intercept callbacks at RESTART/BUDGET_EXHAUSTED/FINAL_CHECK provide the checkpoint mechanism.

2. **How do Galois connections compose across more than two levels?** The theory
   is clean for pairs; transitive composition may lose precision. Is there a
   useful notion of "approximate Galois connection" for lossy levels (numerical
   simulation, LLM reasoning)? The proposal/verify pattern (§5.6 Regime 2)
   sidesteps this by not requiring the connection to be proof-preserving.

3. **When to weaken vs. when to transport?** Given a proof obligation at Level
   5 (Ansatz), when should we weaken to a proposal from Level 1 (numerical) and
   re-verify, vs. transport via a sound Galois connection to Level 4 (SMT)?
   The answer depends on the cost of re-verification vs. the fidelity of the
   lower level. This should itself be learned.

4. **How should elaboration interleave with staging?** When `elaborate`
   encounters a `stage` form, should it: (a) fully elaborate the outer context
   first, then execute inner stages? (b) execute stages eagerly as encountered?
   (c) allow the inner stage to influence elaboration of the outer context
   (bidirectional information flow)? Option (c) is most powerful but hardest to
   implement soundly.

5. **Can we lower Ansatz to refinement types systematically?** If so, we get F*'s
   SMT automation for free on a decidable fragment of Ansatz. The translation
   `∀ (x : T), P x` → `x:T{P(x)}` works for first-order predicates with
   decidable equality. Where exactly is the boundary, and can we detect it
   automatically?

6. **What role do cubical path types play in staging?** Regime 3 (§5.6) suggests
   path types are needed for compositional staging guarantees. But Regime 2
   (propose/verify) works without them. Are there practical cases where we need
   proof transport that can't be handled by re-verification? Higher inductive
   types and quotients are candidates.

7. **SAT/Boolean as the universal bottom.** Every decidable problem reduces to
   SAT. Can we systematically compile decidable Ansatz fragments to SAT (via
   bit-blasting or bounded model checking) as a fallback when SMT theories
   don't apply? This would make the bottom level truly universal.

8. **How does this relate to biological cognition?** The DAG-of-abstractions
   view maps onto hierarchical predictive processing in neuroscience. The
   propose/verify pattern resembles the prediction/error signal loop. Is there
   a useful formal connection, or is this merely analogical?

9. **Solver state as proposal distribution.** The Simplex tableau's dual variables
   quantify the marginal value of each constraint. Can these be used directly as
   importance weights in the SMC framework (§4.3)? If so, the solver's own internal
   heuristics become the proposal distribution for proof search — a form of transfer
   learning from LP to proof theory.

---

## 10. Constraint-Steered Exploration and the Measure-Theoretic Picture

### 10.1 From Oracle Queries to Interactive Constraint Navigation

The original architecture (§3, §5.7) framed solver integration as oracle queries:
delegate a subgoal to SMT, receive SAT/UNSAT, continue. With zustand's persistent
fork semantics now operational, a richer interaction model emerges. The solver is no
longer a black box — it is a navigable state with observable internal structure:

- **Simplex tableau**: the current basis, variable assignments, and bound constraints
- **Dual variables / reduced costs**: the marginal value of relaxing each constraint
  (Rockafellar's generalization of LP duality extends this to convex and non-smooth settings)
- **Conflict explanations**: minimal subsets of assertions that cause infeasibility
  (unsat cores)
- **Branching history**: which variable was split, which direction explored first
  (pseudocost statistics)

This state is the solver's "execution context" — analogous to a proof state's goal
list and local context, or a numerical simulation's current timestep and field values.
Making it observable and forkable turns the solver from an oracle into a **co-reasoning
partner** that can be steered interactively.

### 10.2 Constraint Spaces as Measure Spaces

The category of measures (§3.4) provides the unifying abstraction for heterogeneous
constraint systems:

| System | Constraint | Measure interpretation |
|--------|-----------|----------------------|
| LP/MILP | a·x ≤ b | Indicator on half-space (feasible region) |
| SAT | clause (x₁ ∨ ¬x₂ ∨ x₃) | Indicator on satisfying assignments |
| Probabilistic programming | `observe(data \| model)` | Likelihood weighting |
| Ansatz typing | Γ ⊢ t : T | Support on well-typed terms |
| Numerical simulation | convergence criterion | Approximate indicator (softened) |

All of these constrain a space of possible states. The product of indicators is
conjunction; marginalization is projection; conditioning is Bayesian update. The
key operations of the SMC framework (§4.3) — resampling, proposal, weighting — apply
uniformly when constraints are viewed as (unnormalized) measures.

**LP duality in this picture**: the dual variables of a linear program are the
*Lagrange multipliers* of the constraint measures — they quantify how much the
objective would improve if a constraint were relaxed by one unit. In the SMC
analogy, this is the **importance weight gradient**: which constraint, if softened,
would most increase the probability of finding a feasible solution. This is exactly
the information needed for adaptive budget allocation (§4.3) and routing policy
selection (§5.12).

### 10.3 Cross-Language Projection with Execution State

The fibration picture (§3.3) gains concrete force when projections carry execution
state, not just problem statements:

```
Ansatz proof state                    SMT solver state
  goals: [a ≤ b + c]               tableau: {x₁ = 3x₂ + x₃ - 7}
  lctx: {a : Nat, h : a > 5}       bounds: {x₁ ≥ 0, x₂ ≤ 10}
  mctx: {?m : proof-of-goal}       assignment: {x₁ = 4.2, x₂ = 3.1}
        ↓ project (prop→smt)              ↑ lift (model→witness)
```

The projection Ansatz→SMT translates the goal and hypotheses into SMT constraints,
but also carries the **variable correspondence** (which Ansatz fvar maps to which SMT
variable). The lift SMT→Ansatz carries back not just the SAT/UNSAT answer but the
**model** (for witness construction) or **unsat core** (for proof term reconstruction).

In the MILP setting, the projection additionally carries:
- **Relaxation information**: which integrality constraints were relaxed for the LP bound
- **Cut history**: which Gomory/MIR cuts were generated and applied
- **Branching tree**: the tree of variable splits, with LP bounds at each node

This is the "dragging along execution state" that makes cross-language reasoning
powerful: the SMT solver's search history informs the Ansatz-level proof strategy,
and the Ansatz-level type information constrains the SMT solver's search space.

### 10.4 Interactive REPL-Driven Constraint Exploration

The concrete interaction pattern combines Ansatz proof states with SMT solver states
in a single REPL session:

```clojure
;; Start with a Ansatz proof goal
(def ps (r/prove env '(forall [a Nat] [b Nat]
                         (=> (> a 5) (<= b 3) (< b a)))))

;; Project to SMT: extract arithmetic subgoal
(def [smt-state var-map] (stage/to-smt ps))

;; Inspect solver state: what does the Simplex see?
(stage/simplex-info smt-state)
;; => {:vars {x1 {:value 0, :lower 6, :upper nil, :basic false}
;;            x2 {:value 0, :lower nil, :upper 3, :basic false}}
;;     :status :optimal}

;; Fork and explore: what if we add b >= 2?
(def branch (smt/fork smt-state
              #(-> % (smt/assert-expr [:>= :b 2]) smt/solve)))
;; => {:result :sat, :model {:a 6, :b 2}}

;; Use model as witness, lift back to Ansatz
(def ps' (stage/from-smt-model ps branch var-map))
;; => proof state with concrete witness instantiated

;; Verify through kernel
(r/qed ps')
```

This is not speculative — all the pieces exist:
- `prop->smt` in `ansatz.tactic.decide` translates Ansatz→SMT
- `zustand.smt` provides the fork/solve/model API
- `ansatz.tactic.proof` provides the forkable proof state
- The `stage` functions are the new connective tissue

### 10.5 MILP as Extended Omega

The omega decision procedure (§5.13, now implemented) handles quantifier-free
linear integer arithmetic via Fourier-Motzkin elimination. MILP extends this in
several directions:

- **Branch-and-cut**: when FM elimination produces too many constraints, MILP's
  LP relaxation + branching explores the integer feasible region more efficiently
- **Cutting planes**: Gomory cuts and MIR cuts tighten the LP relaxation,
  potentially proving infeasibility without full enumeration
- **Optimization**: omega proves feasibility/infeasibility; MILP can additionally
  find optimal solutions (useful for constructing witnesses)
- **Pseudocost branching**: the solver learns which variables are expensive to
  branch on, improving search efficiency across related problems

The connection to omega-proof's proof term construction: MILP's branching tree
corresponds to a case split (Or.elim), and each LP bound at a node corresponds
to a linear combination of hypotheses — exactly the structure omega-proof already
builds. The cutting planes correspond to derived inequalities, which can be
reconstructed as chains of arithmetic lemma applications.

### 10.6 Toward Solver-Augmented Programming

The long-term vision extends beyond proof automation. When an LLM (or human
programmer) can observe solver state — the Simplex tableau, the branching
decisions, the dual variables — in the same REPL session where they write code
and construct proofs, several capabilities emerge:

1. **Constraint-guided code generation**: write a specification as constraints,
   explore the feasible region interactively, generate code that implements a
   solution within the feasible region

2. **Proof-guided optimization**: use formal proofs to certify that an
   optimization is correct (the objective is bounded, the constraints are
   satisfiable), then use the optimizer to find the best solution

3. **Scientific computing with formal guarantees**: run a numerical simulation,
   extract convergence conditions as constraints, verify them formally, use the
   verified bounds to guide adaptive mesh refinement

4. **Solver state as LLM context**: embed the current constraint state (active
   constraints, dual values, branching history) into the LLM's context window,
   enabling it to make informed decisions about proof strategy, variable
   selection, and cut generation

This is the "blending solver state into execution state" that transforms
programming from writing instructions to navigating constraint spaces — with
formal verification ensuring that the navigation stays within sound bounds.

## Appendix A: Working Examples (Phase 1 Complete)

### A.1 Interactive Proof: Prop Identity

```clojure
(require '[ansatz.tactic.repl :as r])
(require '[ansatz.kernel.expr :as e])
(require '[ansatz.kernel.level :as lvl])

(def prop (e/sort' lvl/zero))
(def goal (e/forall' "a" prop (e/forall' "h" (e/bvar 0) (e/bvar 1) :default) :default))

(def ps (r/prove env goal))
(r/show-goals ps)
;; Goal 1 of 1:
;;   ⊢ ∀ (a : Prop), a → a

(def ps2 (-> ps (r/intro "a") (r/intro "h") r/assumption))
(r/qed ps2)  ;; => verified proof term (λ a h => h)
```

### A.2 Reflexivity with Init-Medium Environment

```clojure
;; Requires Nat, Eq, Eq.refl from init-medium.ndjson
(def nat (e/const' (name/from-string "Nat") []))
(def eq-aa (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                   nat (e/bvar 0) (e/bvar 0)))
(def goal (e/forall' "a" nat eq-aa :default))

(def ps (-> (r/prove env goal) (r/intro "a") r/rfl))
(r/qed ps)  ;; verified: λ a => @Eq.refl Nat a
```

### A.3 Rewrite: Eq Symmetry

```clojure
;; ∀ (a b : Nat), a = b → b = a
(def ps (-> (r/prove env goal)
            (r/intro "a") (r/intro "b") (r/intro "h")
            (r/rewrite h-fvar false)
            r/rfl))
(r/qed ps)  ;; verified through Java TypeChecker
```

### A.4 Cases: Bool Case Analysis

```clojure
;; ∀ (b : Bool), b = true ∨ b = false
(def ps (-> (r/prove env goal)
            (r/intro "b")
            (r/cases b-fvar-id)))
;; Generates two subgoals: one for Bool.true, one for Bool.false
;; Each closed by constructor + rfl
```

### A.5 Elaboration with Implicit Insertion

```clojure
(require '[ansatz.surface.elaborate :as elab])

;; Without elaborate (manual de Bruijn + explicit everything):
(e/forall' "a" nat (e/app* (e/const' eq-name [u1]) nat (e/bvar 0) (e/bvar 0)) :default)

;; With elaborate (implicit args + universe levels inferred):
(elab/elaborate env '(forall [a Nat] (Eq a a)))
;; => automatically inserts: @Eq.{1} Nat a a

;; Lambda with implicits:
(elab/elaborate env '(lam [a Nat] (Eq.refl a)))
;; => inserts implicit type arg: λ (a : Nat) => @Eq.refl.{1} Nat a

;; @-prefix for fully explicit mode (no implicit insertion):
(elab/elaborate env '(@Eq.{1} Nat a a))
```

### A.6 LLM-Guided Beam Search

```clojure
(def config (r/llm-config {:api-key (System/getenv "FIREWORKS_API_KEY")}))
(r/llm-auto config ps 3 20)
;; LLM suggests tactics, beam search explores top branches
;; Falls back to enumerate-tactics if LLM unavailable
```

### A.7 Test Suite Summary

218 tests, 631 assertions, 0 failures:
- `tactic_test.clj`: proof state, intro, intros, exact, assumption, apply, rfl, constructor, extraction
- `smoke_test.clj`: rewrite + cases with init-medium env, Java TypeChecker verification
- `suggest_test.clj`: trace serialization, prompt formatting, suggestion parsing, LLM integration
- `term_test.clj`: named term builder, de Bruijn conversion, binder syntax
- `pp_test.clj`: pretty-printer, Lean-like output
- `lean_test.clj`: Lean 4 syntax emitter
- `elaborate_test.clj`: implicit insertion, universe inference, @-explicit mode, kernel verification
- `decide_test.clj`: Decidable instance resolution, decide tactic, Ansatz→SMT-LIB translation
- `advanced_test.clj`: omega-proof non-ground tests (implication, Iff, div bounds, mod, Int negation), ring, simp, omega ground
- `match_test.clj`: pattern compilation, nested patterns, Nat literal desugaring
