# Refinement Types for Clojure/JVM

## Building on CIC Kernel + SMT Verification

*Christian Weilbach, March 2026*

---

## 1. Vision

Refinement types express properties that go beyond standard type systems:

```
x : Nat{x > 0}              -- positive natural
v : Vec a n{n <= 1024}       -- bounded-length vector
f : x:Int -> y:Int{y > x}   -- output strictly greater than input
```

The predicate `p` in `x:t{p}` is a CIC proposition, but verification is
delegated to decision procedures (omega, ring, SAT/SMT) rather than requiring
explicit proof terms. This gives us the expressiveness of dependent types with
the automation of SMT-backed refinement checking.

The key insight: cic-clj already has both sides of this equation. The CIC kernel
provides the logical foundation and proof language. The omega/ring/decide tactics
and zustand SMT solver provide the automation. Refinement types are the interface
that connects these to everyday Clojure programming.

**Design principle**: Refinement predicates are always CIC propositions. The SMT
solver produces witnesses that the kernel can check. If the solver fails, the
programmer can fall back to manual proof or weaken the refinement. There is no
separate "refinement logic" -- it is CIC all the way down.


## 2. Architecture

### 2.1 Three-Layer Verification Pipeline

```
Clojure source + refinement annotations
        |
        v
  [Elaboration] -- infer/check refinement types, insert coercions
        |
        v
  [VC Generation] -- weakest precondition / strongest postcondition
        |
        v
  [VC Discharge] -- dispatch to decision procedures:
        |            omega  : linear arithmetic over Nat/Int
        |            ring   : polynomial equalities
        |            decide : propositional / finite domain
        |            SMT    : zustand for combined theories
        |            kernel : full CIC proof search (fallback)
        v
  [Kernel Check] -- all generated proof terms verified by CIC kernel
```

The critical property: the kernel is the final arbiter. Decision procedures
produce *evidence* (proof terms or DRAT certificates) that the kernel validates.
A bug in omega or zustand cannot compromise soundness -- it can only cause a
valid program to be rejected (the solver fails to find a proof).

### 2.2 Refinement Type Syntax

In Clojure surface syntax, refinements attach to existing types:

```clojure
(defn divide [^{:ref (> x 0)} x :- Nat
              ^{:ref (> y 0)} y :- Nat] :- Nat
  (Nat.div x y))

(defn head [^{:ref (> (List.length xs) 0)} xs :- (List a)] :- a
  (List.head xs))
```

In CIC terms, `^{:ref p}` desugars to a sigma type `{x : T // p x}`, but the
elaborator manages projections and injections automatically. The programmer
sees refinement-annotated ordinary types, not dependent pairs.

### 2.3 Subtyping via Implication

Refinement subtyping: `x:t{p} <: x:t{q}` iff `p => q` is provable. This
implication check is the core query dispatched to decision procedures. The
subtyping relation inherits transitivity from logical implication and
reflexivity from `p => p`.

Subtyping queries dominate the verification workload. The dispatch strategy
matters: try omega first for arithmetic, ring for polynomial, decide for
finite, zustand for everything else.


## 3. Phase 1 -- Core Refinement Predicates

### 3.1 Scope

Start with predicates in the theory of linear arithmetic over Nat and Int,
which omega already handles with full proof term generation:

- **Bounds**: `x > 0`, `x < n`, `lo <= x && x < hi`
- **Non-null / non-empty**: `(List.length xs) > 0`, `(String.length s) > 0`
- **Divisibility**: `k | x` (omega-proof already handles dvd)
- **Simple equalities**: `x = c` for constant c

These cover the most common refinement use cases: safe division, safe indexing,
non-empty containers, array bounds.

### 3.2 Implementation Plan

1. **Refinement elaboration**: Extend `elaborate.clj` to parse `{:ref p}` metadata,
   desugar to sigma types internally, and track refinement context (the set of
   in-scope refinement predicates available as hypotheses).

2. **Subtyping oracle**: Given context `G` and query `p => q`, collect arithmetic
   hypotheses from `G`, negate `q`, and call omega. If omega finds a contradiction,
   the implication holds. This is the standard SMT-style validity check.

3. **Automatic strengthening**: At `let` bindings and function entry, infer
   refinements from pattern matches and conditionals. If we branch on `(> x 0)`,
   the true branch has `x : Nat{x > 0}` in context. This is occurrence typing
   extended to refinements -- a natural fit with Typed Clojure's existing
   proposition system.

4. **Safe library wrappers**: Provide refined signatures for core operations:
   `Nat.div` requires non-zero divisor, `List.head` requires non-empty list,
   `Vec.get` requires in-bounds index. These are the payoff -- eliminating
   runtime checks through static verification.

### 3.3 Proof Term Management

omega-proof already generates full CIC proof terms for arithmetic goals. The
refinement checker extracts the proof term and attaches it to the sigma-type
witness. This means every refinement-typed value carries a proof that the kernel
can independently verify.

For performance, proof terms can be erased after kernel checking in compiled
code. The runtime representation of `x : Nat{x > 0}` is just a Nat.


## 4. Phase 2 -- VC Generation

### 4.1 Dijkstra Monads for Clojure Effects

Clojure is effectful: mutable state, IO, exceptions, concurrency. To reason
about refinement-typed effectful code, we need verification condition (VC)
generation that accounts for effects.

F* solves this with Dijkstra monads: each effect (State, IO, Exception) has a
*specification monad* that computes weakest preconditions. The key idea is that
the WP transformer is itself a pure function in the type theory, so it composes.

For Clojure, the relevant effects are:

- **Pure**: trivial WP, `wp(e, Q) = Q(e)`
- **Exception**: `wp(throw, Q) = True` (any postcondition holds vacuously after throw)
- **State**: `wp(swap! r f, Q) = forall s. Q(f s)(update r f s)`
- **IO**: opaque, no refinement propagation (but can assert postconditions)

### 4.2 WP Calculus

Given a function body, compute the weakest precondition for the declared
postcondition (the output refinement). The VC is: precondition => WP.

```
wp(let x = e1 in e2, Q) = wp(e1, fun v -> wp(e2[x:=v], Q))
wp(if c then e1 else e2, Q) = (c => wp(e1, Q)) /\ (not c => wp(e2, Q))
wp(f(args), Q) = f.pre(args) /\ (forall r. f.post(args, r) => Q(r))
```

The generated VCs are CIC propositions. They go through the same dispatch:
omega for arithmetic, ring for polynomial, zustand for combined theories.

### 4.3 Loop Invariants

Clojure idiom favors recursion and higher-order functions over imperative loops.
`reduce`, `map`, `filter` get refinement-polymorphic specifications:

```
reduce : (b -> a -> b{inv}) -> b{inv} -> [a] -> b{inv}
```

where `inv` is an abstract refinement (Phase 3) that the step function
preserves. This avoids explicit loop invariant annotation for the common case.

For `loop/recur`, the programmer provides an invariant or the system attempts
to infer one from the initial values and the recur expressions.


## 5. Phase 3 -- Abstract Refinements

### 5.1 Parametric Refinement Polymorphism

Liquid Haskell's abstract refinements allow refinement predicates to be
parameters, enabling precise specification of higher-order functions:

```
max : forall p q. x:Int{p} -> y:Int{q} -> Int{p \/ q}
compose : forall p q r. (y:b{q} -> c{r}) -> (x:a{p} -> b{q}) -> a{p} -> c{r}
```

In CIC, abstract refinements are simply universally quantified propositions.
The expressiveness comes for free from dependent types. The challenge is
*inference*: determining which abstract refinements to instantiate at call sites.

### 5.2 Inference via Liquid Typing

The Liquid Types inference algorithm:
1. Assign template refinements with unknown predicate variables to each program point
2. Generate subtyping constraints from the program
3. Solve constraints by abstract interpretation over a finite predicate domain

The predicate domain (called "qualifiers") is drawn from the program text:
function preconditions, branch conditions, and user-provided hints. This keeps
inference decidable while being expressive enough for most practical cases.

### 5.3 Connection to CIC Proof Search

When Liquid inference fails (the predicate domain is too coarse), the system
can escalate to CIC proof search. The tactics (omega, ring, simp) serve as
specialized solvers. The grind tactic in Lean, which combines congruence
closure with case splitting, is a model for the kind of general-purpose
automation that fills gaps between specialized solvers.

This graceful degradation -- Liquid inference for the common case, tactic-based
proof search for hard cases, manual proof for the rest -- is the key usability
property.


## 6. Phase 4 -- Integration

### 6.1 Typed Clojure

Typed Clojure has occurrence typing: after `(if (number? x) ... ...)`, the type
of `x` is narrowed in each branch. Refinement types generalize this: after
`(if (> x 0) ... ...)`, the refinement of `x` is strengthened.

Integration path:
- Typed Clojure's proposition system already tracks path-sensitive type info
- Extend propositions to carry refinement predicates
- Typed Clojure's malli provider model gives runtime schemas; refinements are
  the static counterpart with the same shape
- Typed Clojure handles structural subtyping; refinement checking adds the
  predicate implication layer on top

### 6.2 Methodic/Romeo

The Julia-style multiple dispatch in methodic already has a type lattice
(Magma -> Ring -> Field). Refinements add value-dependent dispatch:

```julia
# methodic pseudo-syntax
function norm(x::Vec{Float64, n} where n > 0) :: Float64{result >= 0}
```

Connection points:
- CAS rewrite rules in methodic produce polynomial equalities -- ring tactic
  verifies these
- Method resolution with refinement types: dispatch considers refinement
  subtyping, not just nominal subtyping
- Valhalla value classes for zero-alloc refined primitives (the refinement is
  erased at runtime, the underlying primitive is unboxed)

### 6.3 Malli Schemas

Malli schemas describe data shapes at runtime. Refinement types describe them
at compile time. The bridge:

```clojure
;; malli schema
[:int {:min 1, :max 100}]

;; corresponding refinement type
x : Int{1 <= x && x <= 100}
```

Generate malli schemas from refinement types for runtime validation at system
boundaries (API endpoints, deserialization). Generate refinement types from
malli schemas for static checking of internal code. The two representations
are projections of the same specification.


## 7. Open Questions

### 7.1 Gradual Refinement Typing

Not all code needs to be verified. Gradual refinement types allow mixing
refined and unrefined code:

- At the boundary, insert dynamic checks (malli validators)
- Unrefined code is trusted (refinement `True`)
- The blame calculus tracks which module is responsible when a dynamic check fails

This is essential for incremental adoption in existing Clojure codebases.
The open question is how to make the gradual boundary efficient -- malli
validation is not free, and hot paths may cross the boundary frequently.

### 7.2 Inference Completeness

Liquid Types inference is complete for a fixed qualifier domain. But choosing
the right qualifiers is an art. Possible approaches:

- Mine qualifiers from spec assertions and test predicates
- Use LLM suggestion (cic-clj already has llm.clj/suggest.clj) to propose
  candidate refinements
- Abductive inference: given a failing VC, find the weakest missing hypothesis

### 7.3 Decidability Boundaries

The omega/ring/decide tactics handle decidable fragments. But useful refinements
often straddle decidability boundaries:

- Nonlinear arithmetic (undecidable in general, but omega handles ground cases
  and ring handles polynomial equalities)
- Heap properties (reachability, separation) -- requires separation logic
  extensions
- Concurrency (linearizability, lock ordering) -- requires specialized logics

The design must be honest about these boundaries. When a VC falls outside the
decidable fragment, the system should say so clearly and offer alternatives
(manual proof, runtime check, weaker refinement).

### 7.4 Performance

VC generation and discharge add compile-time cost. Benchmarks needed:

- omega-proof on typical arithmetic VCs (currently handles Mathlib-scale proofs)
- zustand on combined-theory queries (EUF + LIA + arrays)
- Liquid inference fixpoint computation on realistic Clojure programs

The escape hatch is always available: drop the refinement, accept a runtime check.

### 7.5 Incremental Checking

Large Clojure projects recompile incrementally. Refinement checking must be
incremental too: when a function body changes but its refinement signature
doesn't, downstream code doesn't need rechecking. This mirrors the separate
compilation story in Lean (only re-elaborate declarations whose dependencies
changed).


## 8. Connections to Existing Infrastructure

### 8.1 omega-proof for Arithmetic VCs

omega-proof is the workhorse for Phase 1. It already handles:
- Linear inequalities over Nat and Int
- Nat.sub dichotomy (a - b = 0 when a <= b)
- Divisibility constraints
- Full proof term generation with justification tracking
- Negation normal form, Fourier-Motzkin elimination, GCD tests

The remaining gaps (dvd proof terms, Nat.sub proof terms) are on the
implementation roadmap and directly block refinement type features.

### 8.2 SAT/DRAT for Combinatorial Properties

sat-clj provides SAT solving with DRAT proof certificates. The DRAT-to-CIC
proof reconstruction path means SAT-backed refinements also produce kernel-
checkable evidence. Use cases:

- Bitvector arithmetic (overflow checking, mask properties)
- Finite-domain constraint satisfaction
- Configuration validity (feature models, permission lattices)

### 8.3 ring for Polynomial Equalities

The ring tactic normalizes polynomial expressions to grevlex sparse form.
Refinements like `x * x >= 0` or `(a + b)^2 = a^2 + 2*a*b + b^2` are
verified by normalization + decide. This extends to the CAS in methodic:
algebraic simplification rules produce polynomial identities that ring
certifies.

### 8.4 simp for Rewriting

simp performs bottom-up rewriting with a lemma index. In the refinement
pipeline, simp simplifies VCs before dispatching to omega or SMT. A VC like
`List.length (List.cons x xs) > 0` simplifies to `Nat.succ (List.length xs) > 0`
which omega handles immediately.

### 8.5 zustand / SMT Integration

zustand combines theories (EUF, LIA, arrays) with DPLL(T) search. For
refinement types, the combined theory is essential: VCs typically mix arithmetic
with uninterpreted functions (user-defined predicates) and data structure
operations. The SMT solver is the catch-all when specialized tactics don't
apply.

The proof reconstruction path (SMT proof -> CIC proof term) is the main
engineering challenge. F* sidesteps this by trusting Z3. We don't -- the kernel
checks everything. This is more work but gives a stronger guarantee.


## 9. Research Priorities

Ordered by dependency and payoff:

1. **Refinement elaboration** (Phase 1): Get `x : Nat{x > 0}` working end-to-end
   with omega discharge and kernel-checked proof terms. This is the minimum
   viable demonstration.

2. **Occurrence typing integration**: Connect refinement context to conditional
   branches. After `(when (pos? x) ...)`, the body sees `x : Nat{x > 0}`.

3. **Safe library layer**: Refined signatures for 20-30 core functions (division,
   indexing, head/tail, string operations). Measure how many common runtime
   errors become compile-time errors.

4. **WP generation for pure code**: Compute VCs for let-bindings, conditionals,
   and function calls. No effects yet.

5. **Liquid inference prototype**: Qualifier mining from function signatures and
   branch conditions. Measure inference coverage on real Clojure code.

6. **Effect WP** (Phase 2): State and exception monads. Atoms as refined mutable
   references.

7. **Abstract refinements** (Phase 3): Parametric predicates for higher-order
   functions. This unlocks `map`, `filter`, `reduce` with precise specifications.

8. **Malli bridge** (Phase 4): Bidirectional translation between refinement types
   and malli schemas. Gradual typing at module boundaries.

---

*This plan builds on the adaptive reasoning architecture (see
`research-design-adaptive-reasoning.md`) where refinement types are the
interface between the CIC verification kernel and everyday programming. The
decision procedure hierarchy (omega < ring < SAT < SMT < CIC proof search)
provides the automation backbone. The kernel provides the trust anchor.*
