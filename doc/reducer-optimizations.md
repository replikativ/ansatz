# Verified Reducer Optimizations

This document describes the design direction for `ansatz.reducers`: a
Clojure-shaped reducer/transducer API where Ansatz can apply optimizations that
ordinary Clojure cannot safely assume, because the optimizer can require
kernel-checked laws.

## Starting Point

Clojure transducers already deforest ordinary sequence pipelines. A composed
transducer such as:

```clojure
(comp (map inc) (filter odd?) (map #(* % %)))
```

does not allocate intermediate lazy sequences or intermediate collections when
used with `transduce`, `into`, or `eduction`. Therefore, Ansatz should not claim
that its main optimization value is "skipping lazy seqs". Clojure already does
that for transducer-aware terminals.

The current Ansatz reducer prototype instead provides:

- An explicit pipeline AST for Clojure-like `map`, `filter`, `remove`, `cat`,
  and `mapcat`.
- A compiled transducer path for normal Clojure execution.
- Law-carrying monoid specs for safe `reducers/fold` regrouping.
- A small internal optimizer that canonicalizes adjacent `map`/`filter` steps
  and records the rewrite laws it used.
- `ReducerLawSpec` and `certified-fn` scaffolding, so the optimizer can
  distinguish unchecked Clojure closures from kernel-validated function
  metadata and kernel-validated rewrite theorem types.

The design goal is to turn these pieces into a proof-carrying optimizer, without
pretending that arbitrary Clojure closures are CIC terms.

## Core Distinction

There are three different levels of trust:

1. **Ordinary Clojure pipeline**

   The user supplies arbitrary Clojure functions and predicates. These may have
   side effects, throw, depend on time, mutate state, or observe evaluation
   order. Ansatz may still compile them to efficient transducers, but it must
   only apply rewrites that preserve Clojure evaluation order exactly.

2. **Law-checked pipeline shape**

   The optimizer rule schema is validated against kernel theorems. For example,
   the kernel can check that `map f` followed by `map g` is denotationally equal
   to `map (g . f)` for pure functions. This validates the rule, but it does not
   by itself prove that a particular Clojure closure is the kernel function `f`.

3. **Certified pipeline**

   Each function, predicate, terminal, and algebraic structure in the pipeline
   has a kernel expression and a runtime implementation linked by the Ansatz
   compiler or an explicit trusted bridge. In this mode, the optimizer can
   produce or cite a checked proof that the optimized pipeline has the same
   denotation as the original.

The useful verified optimizations live mostly in the third level.

## Semantics to Prove First

The first verified subset should be smaller than full Clojure transducers.

Recommended initial semantics:

- Inputs are finite sequences/lists.
- Pipeline functions are pure and total.
- `map`, `filter`, and `remove` are modeled by their ordinary list semantics.
- Sequential terminals are modeled as `foldl`/`foldMap`.
- Parallel terminals are allowed only through checked monoid or semiring laws.
- Early termination via `reduced`, completion arities, exceptions, chunked seq
  artifacts, and stateful transducers are outside the first proof surface.

This subset is intentionally conservative. It lets us prove useful optimizations
without first formalizing the entire Clojure transducer protocol.

## Kernel Theory

The reducer theory should enter Ansatz as ordinary Lean/Ansatz declarations, not
as special kernel rules. The kernel remains unchanged.

At minimum, define a small reducer DSL in Lean/Ansatz terms:

```lean
inductive Pipe where
  | id
  | map
  | filter
  | remove
  | comp

def denote : Pipe -> List a -> List b
```

The exact encoding can be typed more precisely than this sketch, but the key is
that every pipeline has a denotation as a pure function over finite lists.

Then prove rewrite theorems such as:

```lean
map_map :
  denote (map f >>> map g) xs =
  denote (map (fun x => g (f x))) xs

filter_filter :
  denote (filter p >>> filter q) xs =
  denote (filter (fun x => p x && q x)) xs

remove_filter :
  denote (remove p) xs =
  denote (filter (fun x => not (p x))) xs
```

For terminal-aware optimization, prove laws over folds:

```lean
fold_map_hom :
  foldMap M f (xs ++ ys) =
  combine (foldMap M f xs) (foldMap M f ys)

fold_map_map :
  foldMap M f (map g xs) =
  foldMap M (fun x => f (g x)) xs

sum_map :
  sum (map f xs) =
  foldl (fun acc x => acc + f x) 0 xs
```

These theorems should be imported through the same `lean4export`/kernel replay
path as Mathlib and CSLib declarations.

## Clojure API Shape

Keep the existing pragmatic API:

```clojure
(r/pipeline
  (map inc)
  (filter odd?)
  (map #(* % %)))
```

This path remains Clojure-compatible. It may run the conservative optimizer, but
its `r/explain` trace must continue to show unchecked rewrite metadata unless
the involved laws and functions are certified.

Add a certified function wrapper:

```clojure
(r/certified-fn
  {:name 'Nat.succ
   :type '(Nat -> Nat)
   :kernel-term 'Nat.succ
   :runtime inc})
```

The actual API can be more compact, but every certified function needs:

- A kernel name or kernel expression.
- A kernel type.
- A runtime implementation.
- A validation status proving that the kernel side is well-typed.
- A clear trust boundary explaining why the runtime implementation corresponds
  to the kernel expression.

Then add a checked pipeline entry point:

```clojure
(-> (r/pipeline
      (map nat-succ)
      (filter nat-odd?)
      (map nat-square))
    (r/checked env)
    (r/into [] xs))
```

The current implementation calls this step `r/check-pipeline` and expects
validated reducer law specs. It marks a rewrite `:kernel-checked? true` only
when the rewrite theorem type was checked and all functions involved in that
rewrite carry kernel-validated certification metadata.

In checked mode, Ansatz can distinguish:

- `:kernel-checked? true` rewrites, justified by imported theorem types.
- `:runtime-trusted? true` bridges, justified by compiler/runtime metadata.
- rejected rewrites, where the pipeline contains arbitrary Clojure code.

## Law Validation

The reducer law validator should mirror the existing `MonoidSpec` machinery.

Introduce something like:

```clojure
(defrecord ReducerLawSpec [rule theorem expected-type metadata])
```

Validation should:

1. Resolve `theorem` in the kernel environment.
2. Generate the expected theorem type for the rule.
3. Ask the `TypeChecker` whether actual and expected theorem types are
   definitionally equal.
4. Mark the law as kernel-checked if the comparison succeeds.

This validates the rewrite schema. It should not silently validate arbitrary
Clojure closures.

For per-pipeline certification, the optimizer should later produce a proof plan
or proof term:

```clojure
{:original original-pipeline
 :optimized optimized-pipeline
 :proof proof-term
 :theorem-type (= (denote original-pipeline)
                  (denote optimized-pipeline))}
```

The kernel then checks that proof term before the optimized pipeline is marked
certified.

## Optimizations Worth Proving

The strongest payoff is not local transducer fusion. It is optimizations that
require semantic assumptions Clojure cannot make for arbitrary functions.

### Lawful Parallel Regrouping

`reducers/fold` is only semantics-preserving when the terminal operation is
associative and has an identity. Ansatz can require checked monoid laws before
using parallel regrouping.

Examples:

- `sum` over Nat/Int addition.
- `product` over multiplication.
- `frequencies` over map union with additive counts.
- `group-by` over per-key monoids.

### Terminal-Aware Specialization

Compile a pipeline and terminal together instead of compiling a generic
transducer first.

Examples:

- `(pipeline (map f) (filter p)) + sum` becomes one tight accumulator loop.
- `frequencies` specializes to direct key counting.
- `group-by` specializes to direct per-key monoid accumulation.
- Primitive Nat/Int terminals can use primitive JVM accumulators where safe.

These optimizations should be justified by fold/foldMap theorems and guarded by
runtime overflow/boxing policy.

### Purity-Gated Reordering

For arbitrary Clojure functions, reordering is unsound. For certified pure
functions and predicates, useful rewrites become available.

Examples:

- Push `filter` before expensive `map` when a theorem relates the predicate to
  the original input.
- Combine predicates.
- Eliminate redundant predicates using implication/idempotence proofs.
- Move projections before construction when the theorem says the field is
  unchanged.

### Algebraic Simplification

Use algebraic laws attached to the terminal structure.

Examples:

- Drop `map identity`.
- Drop `filter (constantly true)`.
- Replace `filter (constantly false) + sum` with the monoid identity.
- Fuse adjacent affine maps over Int/Nat when the arithmetic proof is available.
- Use annihilators, identities, idempotence, and distributivity where the
  terminal algebra provides checked laws.

### Query-Like Pushdown

For associative per-key aggregation, many database-style rewrites are possible:

- Push filters before grouping.
- Push key projection before value aggregation.
- Combine multiple aggregations over the same traversal.
- Pre-aggregate chunks and merge with checked per-key monoids.

These are likely better payoffs than more local transducer fusion.

## Compilation Strategy

Use three backends, selected by certification level and terminal:

1. **Generic transducer backend**

   Preserve today's behavior. This is the default for ordinary Clojure code.

2. **Specialized sequential backend**

   Generate a terminal-specific loop for checked or shape-safe pipelines. This
   avoids generic transducer call layering and can use primitive accumulators.

3. **Specialized parallel backend**

   Use `reducers/fold` or future fork/join kernels only when the terminal laws
   are checked. The combine operation must be associative and have a checked
   identity.

The optimizer should choose the strongest backend it can justify, and
`r/explain` should report why.

## Explainability

`r/explain` should become the main debugging and trust UI.

It should report:

- Original pipeline steps.
- Optimized pipeline steps.
- Backend selected.
- Rewrites applied.
- The theorem used for each rewrite.
- Whether the theorem type was kernel-checked.
- Whether all involved functions are certified.
- Runtime trust boundaries.
- Rewrites that were intentionally skipped and why.

Example:

```clojure
{:backend :specialized-sequential
 :rewrites [{:rule :fold-map-map
             :theorem 'Ansatz.Reducer.fold_map_map
             :kernel-checked? true
             :functions-certified? true}]
 :skipped [{:rule :filter-map-pushdown
            :reason :missing-predicate-map-commutation-proof}]}
```

## Validation Plan

Validation should happen at four levels:

1. Unit tests comparing ordinary Clojure semantics on side-effectful functions
   for the unchecked API.
2. Kernel tests proving and validating reducer law theorem types.
3. Differential tests comparing generic transducer output and specialized
   backend output for generated pure pipelines.
4. Benchmarks that separate allocation savings, call-layer savings, primitive
   specialization, and parallel regrouping.

The first benchmark question should not be "did we avoid lazy seqs?" It should
be:

- Did terminal specialization beat generic transduce?
- Did checked parallel regrouping beat sequential execution at realistic sizes?
- Did a proof-gated rewrite remove real work?
- Did the certified path add acceptable validation overhead?

## Roadmap

1. Keep the current optimizer described as conservative canonicalization for
   unchecked Clojure code.
2. Extend the reducer theory with real Lean/Ansatz declarations for the
   optimizer laws sketched above.
3. Use `ReducerLawSpec` and `certified-fn` to validate rewrite theorem types
   and function declarations against an imported environment.
4. Mark optimizer rewrites checked only when the rule and involved functions are
   certified.
5. Add terminal-specific sequential compilation for `sum`, `frequencies`, and
   `group-by`.
6. Add proof-backed parallel regrouping beyond the current monoid specs.
7. Add per-pipeline proof production once the reducer DSL and theorem library
   are stable.

## Non-Goals

- Do not replace Clojure transducers for ordinary pipelines.
- Do not claim arbitrary Clojure closures are pure.
- Do not reorder effectful operations.
- Do not model full `reduced`/completion semantics before the pure finite-list
  reducer theory is useful.
- Do not add optimizer-specific kernel privileges. All guarantees should come
  from ordinary theorem declarations checked by the existing kernel.
