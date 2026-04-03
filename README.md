# Ansatz

**Write Clojure. Prove it correct. Run at native speed.**

Ansatz is a verified programming library for Clojure built on the [Calculus of Inductive Constructions](https://en.wikipedia.org/wiki/Calculus_of_inductive_constructions) (CIC) — the same type theory that powers [Lean 4](https://lean-lang.org/). It implements Lean 4's kernel in Java, type-checks proofs against [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) (210k+ theorems, 648k declarations) and [CSLib](https://github.com/leanprover/cslib) (verified algorithms), and compiles verified functions to native Clojure.

**Same kernel, different surface.** Ansatz shares Lean 4's CIC kernel — a proof verified in Ansatz is valid in Lean 4 and vice versa. Proofs can be [exported to Lean 4](doc/lean4-for-clojurians.md) syntax. The difference is the surface language: Lean 4 uses its own syntax; Ansatz uses Clojure s-expressions and runs on the JVM. See **[Lean 4 for Clojurians](doc/lean4-for-clojurians.md)** for the full comparison, translation guide, and learning path.

```clojure
(require '[ansatz.core :as a])
(a/init! "/var/tmp/ansatz-cslib" "cslib")

;; Verified merge sort — kernel-checked, compiles to Clojure
(a/defn merge [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  :termination-by (+ (List.length xs) (List.length ys))
  (match xs (List Nat) (List Nat)
    (nil ys)
    (cons [x xs']
      (match ys (List Nat) (List Nat)
        (nil (cons x xs'))
        (cons [y ys']
          (if (<= x y)
            (cons x (merge xs' (cons y ys')))
            (cons y (merge (cons x xs') ys'))))))))

;; Run it — it's a normal Clojure function
(merge '(1 3 5) '(2 4 6)) ;; => (1 2 3 4 5 6)

;; Structures compile to Clojure defrecord
(a/structure Point [] (x Nat) (y Nat))
(->Point 3 4)  ;; => #user.Point{:x 3, :y 4}
(:x (->Point 3 4))  ;; => 3
```

**Verified data structures** — define types, implement with pattern matching, prove properties:

```clojure
;; Define your own types (like Clojure records, but type-checked)
(a/inductive RBColor [] (red) (black))
(a/inductive RBTree [α Type]
  (leaf)
  (node [color RBColor] [left (RBTree α)] [key α] [right (RBTree α)]))

;; Pattern matching with recursion — the kernel checks termination
;; ih_left and ih_right are induction hypotheses (recursive results)
(a/defn rb-size [t (RBTree Nat)] Nat
  (match t (RBTree Nat) Nat
    (leaf 0)
    (node [color left key right] (+ 1 (+ ih_left ih_right)))))

;; Nested match for BST lookup — references outer param k
(a/defn rb-member [t (RBTree Nat) k Nat] Bool
  (match t (RBTree Nat) Bool
    (leaf false)
    (node [color left key right]
      (match (< k key) Bool Bool
        (true ih_left)                    ;; recurse into left subtree
        (false (match (== k key) Bool Bool
                 (true true)              ;; found it
                 (false ih_right)))))))   ;; recurse into right subtree

;; All verified functions compile to native Clojure and run at full speed
(rb-size tree)           ;; => 10
(rb-member tree 4)       ;; => true
(rb-member tree 42)      ;; => false
```

**Prove properties** — from simple definitional equality to automated reasoning:

```clojure
;; Simplest proof: rb-size(leaf) computes to 0 by definition.
;; (rfl) = "reflexivity" — both sides reduce to the same thing.
(a/theorem leaf-size-zero []
  (= Nat (rb-size (RBTree.leaf Nat)) 0)
  (rfl))

;; (omega) solves linear arithmetic over natural numbers automatically.
;; It sees: goal is (rb-size l) ≤ 1 + (rb-size l) + (rb-size r)
;; and closes it because x ≤ 1 + x + y for all naturals.
(a/theorem left-le-size [c :- RBColor, l :- (RBTree Nat), k :- Nat, r :- (RBTree Nat)]
  (<= Nat (rb-size l) (+ 1 (+ (rb-size l) (rb-size r))))
  (omega))

;; Induction + grind: the standard pattern for list properties.
;; (induction l) splits into two goals:
;;   1. Base case:  llen (lmap f []) = llen []        — both sides are 0
;;   2. Inductive:  llen (lmap f (x::xs)) = llen (x::xs)
;;      with IH:    llen (lmap f xs) = llen xs
;; (grind "lmap" "llen") tells grind to use the equation theorems
;; for lmap and llen (e.g. llen.eq_2: llen(x::xs) = 1 + llen xs).
;; It unfolds one step, sees 1 + llen(lmap f xs) = 1 + llen xs,
;; and closes via congruence from the IH.
(a/theorem map-preserves-len [f :- (arrow Nat Nat), l :- (List Nat)]
  (= Nat (llen (lmap f l)) (llen l))
  (induction l) (all_goals (grind "lmap" "llen")))

;; Sorted is an indexed inductive: Sorted [] | Sorted [a] | Sorted (a::b::tl) when a≤b.
;; (induction h) on h : Sorted l gives 3 goals (one per constructor).
;; (grind "insertSorted") uses insertSorted's equation theorems to unfold it,
;; case-splits on ≤ comparisons, applies constructors, uses omega
;; for arithmetic, and the IH for the recursive case.
(a/theorem insert-preserves
  [x :- Nat, l :- (List Nat), h :- (Sorted l)]
  (Sorted (insertSorted x l))
  (induction h) (grind "insertSorted"))

;; balance1 has 7 branches (from nested pattern matching on color + subtree shape).
;; (cases hl) splits ValidRB(l) into leaf/node.
;; (simp "balance1") uses balance1's equation theorems to unfold it for each branch.
;; (grind) then applies ValidRB constructors and matches sub-proofs from context.
;; The middle lines split further on color, subtree shape, and inner color
;; to expose the left-left rotation case (the only one that restructures the tree).
(a/theorem balance1-preserves-valid
  [l :- (RBTree Nat), v :- Nat, r :- (RBTree Nat),
   hl :- (ValidRB l), hr :- (ValidRB r)]
  (ValidRB (balance1 l v r))
  (cases hl)                           ;; leaf or node?
  (all_goals (try (simp "balance1")))  ;; unfold via equation theorems
  (all_goals (try (grind)))            ;; close the easy cases
  (all_goals (try (cases c)))          ;; red or black?
  (all_goals (try (cases l)))          ;; left subtree shape
  (all_goals (try (cases color)))      ;; inner node color (detects LL rotation)
  (all_goals (try (cases hl)))         ;; decompose inner ValidRB proof
  (all_goals (try (simp "balance1")))  ;; unfold the rotation case
  (all_goals (try (grind))))           ;; close all remaining goals
```

See [examples/](examples/) for complete working examples:
- **[verified_list.clj](examples/verified_list.clj)** — verified list library (map, filter, append, length) with 10+ proved properties + insertion sort correctness
- **[sorting.clj](examples/sorting.clj)** — verified merge sort, structures, factorial (CSLib-inspired)
- **[rbtree.clj](examples/rbtree.clj)** — verified red-black tree with balance invariant proof (grind + manual versions)
- **[gradient_descent.clj](examples/gradient_descent.clj)** — verified GD convergence rate proofs
- **[metaprogramming.clj](examples/metaprogramming.clj)** — custom tactics, elaborators, simprocs

**New to verified programming?** Start with the **[Tutorial](doc/tutorial.md)** — a hands-on guide that teaches you to define functions, write proofs, and use `grind`, with no prior theorem proving experience needed.

Already know Lean 4? See **[Lean 4 for Clojurians](doc/lean4-for-clojurians.md)** for the syntax translation guide.

### How it works (for Clojure developers)

Ansatz adds these primitives to Clojure:

1. **`a/defn`** — like `defn`, but type-checked. The kernel verifies that your function matches its type signature. Supports well-founded recursion via `:termination-by` for non-structural patterns (merge sort, factorial). The compiled output is a normal Clojure `fn`.

2. **`a/theorem`** — states a property and proves it using *tactics*. Tactics are commands that build a proof step by step. The `(grind "defn-name")` tactic automates most proofs via E-graph congruence closure and case splitting. For manual control: `(apply lemma)`, `(induction x)`, `(cases h)`, `(omega)`, `(simp "lemma")`. The kernel verifies the final proof term.

3. **`a/inductive`** — defines algebraic data types with exhaustive pattern matching. The kernel generates a recursor that ensures termination.

4. **`a/structure`** — defines record types that compile to Clojure `defrecord`. Fields are accessible via keywords: `(:x point)`. Kernel-verified projections are auto-generated.

The key idea: Lean 4's Mathlib library has 210,000+ proved theorems about math (algebra, analysis, topology). Ansatz lets you USE those theorems in your Clojure proofs. When you write `(apply mul_le_of_le_one_left)`, you're applying a theorem that was proved in Mathlib and verified by the kernel. Proofs are portable — Ansatz can [export to Lean 4 syntax](doc/lean4-for-clojurians.md) and Lean 4 proofs can be imported into Ansatz.

## Features

- **Verified functions** — define functions with CIC types, prove properties, run at JVM speed
- **Grind tactic** — automated reasoning via persistent E-graph with congruence closure, propositional propagators (And/Or/Not/Eq/ite), E-matching for lemma instantiation, constructor injection/discrimination, and theory solver integration
- **Well-founded recursion** — `:termination-by` for non-structural patterns (merge sort, factorial)
- **Structures** — `a/structure` compiles to `defrecord` with keyword access and pretty-printing
- **Generic types** — implicit type parameter inference via auto-elaborate (polymorphic constructors work without explicit type annotations)
- **Lean 4 Mathlib + CSLib** — 648k Mathlib declarations + CSLib verified algorithms
- **Tactic proofs** — `apply`, `simp`, `omega`, `ring`, `grind`, `assumption`, `induction`, `cases`, and more
- **Instance synthesis** — automatic typeclass resolution with tabled backtracking
- **Compiled output** — verified `defn` compiles to native Clojure `fn` with arity-aware flat calls
- **Extensible** — register custom tactics, elaborators, and simprocs with full kernel access
- **Immutable proof state** — free backtracking via Clojure persistent data structures

## Quick Start

### Prerequisites

- Java 21+ (for Foreign Function API / memory mapping)
- [Clojure CLI](https://clojure.org/guides/install_clojure) 1.12+

### Installation

Add to `deps.edn`:

```clojure
{:deps {org.replikativ/ansatz {:mvn/version "0.1.0-SNAPSHOT"}}}
```

### Setup Mathlib Store

Ansatz needs a store of Lean 4 Mathlib declarations. There's a one-command setup script:

**Automated setup (recommended)**

```bash
# Requires: Lean 4 (elan), Java 21+, Clojure CLI
./scripts/setup-mathlib.sh
```

This clones `lean4export` and `mathlib4` (if not present), exports Mathlib to NDJSON,
generates the instance registry, and imports into an Ansatz store at `/var/tmp/ansatz-mathlib`.
Takes ~20 minutes on first run.

**Manual setup**

If you prefer step-by-step:

```bash
# 1. Clone and build lean4export (https://github.com/leanprover/lean4export)
git clone https://github.com/leanprover/lean4export.git ../lean4export
cd ../lean4export && lake build

# 2. Export Mathlib to NDJSON (~5 min, ~5GB)
.lake/build/bin/lean4export --mathlib > ../ansatz/test-data/mathlib.ndjson

# 3. Generate instance registry from Mathlib (~2 min)
cd ../mathlib4
lake env lean DumpInstances.lean   # produces instances.tsv
cp instances.tsv ../ansatz/resources/instances.tsv

# 4. Import into Ansatz store (~15 min)
cd ../ansatz
clj -M -e '
(require (quote [ansatz.export.storage :as s]))
(def store (s/open-store "/var/tmp/ansatz-mathlib"))
(s/import-ndjson-streaming! store "test-data/mathlib.ndjson" "mathlib" :verbose? true)
'
```

### Setup CSLib Store (Verified Algorithms)

[CSLib](https://github.com/leanprover/cslib) is the official Computer Science library for Lean 4 — verified sorting, automata, lambda calculus, and more.

```bash
./scripts/setup-cslib.sh
```

This imports CSLib (including its Mathlib dependency) into a store at `/var/tmp/ansatz-cslib`.

**Using init-medium for quick testing (no Lean needed)**

The test data `test-data/init-medium.ndjson` (10MB, 2997 declarations) is included
in the repo and sufficient for basic proofs on Nat. No Mathlib setup required:

```clojure
;; Works out of the box for Nat proofs (no Real/analysis)
(require '[ansatz.export.storage :as s] '[ansatz.export.replay :as r]
         '[ansatz.export.parser :as p])
(def env (:env (r/replay (:decls (p/parse-ndjson-file "test-data/init-medium.ndjson")))))
```

### Initialize and Prove

```clojure
(require '[ansatz.core :as a])

;; Load Mathlib environment
(a/init! "/var/tmp/ansatz-mathlib" "mathlib")

;; Define and prove
(a/defn double [n :- Nat] Nat (+ n n))

(a/theorem add-zero [n :- Nat]
  (= Nat (+ n 0) n)
  (simp "Nat.add_zero"))

(double 21) ;; => 42
```

## Syntax Reference

### Types

```clojure
Nat                          ;; natural numbers
Int                          ;; integers
Real                         ;; real numbers
Bool                         ;; booleans
Prop                         ;; propositions
Type                         ;; types
(List Nat)                   ;; lists
```

### Operators

```clojure
(+ a b)                      ;; Nat addition (default)
(add Real a b)               ;; typed addition
(mul Real a b)               ;; typed multiplication
(sub Real a b)               ;; subtraction
(div Real a b)               ;; division
(pow Real k n)               ;; power (base^Nat)
(= Nat a b)                  ;; equality (Prop)
(le Real a b)                ;; ≤ (Prop)
(<= Real a b)                ;; ≤ sugar (Prop, 3-arg form)
(<= a b)                     ;; ≤ (Bool, Nat default, 2-arg form)
```

### Definitions

```clojure
;; Verified function (structural recursion)
(a/defn name [param :- Type, ...] ReturnType body)

;; Well-founded recursion (non-structural, e.g. merge sort)
(a/defn merge [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  :termination-by (+ (List.length xs) (List.length ys))
  body)

;; Typeclass params
(a/defn sort [α :- Type, inst :- (Ord α) :inst, xs :- (List α)] (List α) ...)

;; Theorem
(a/theorem name [param :- Type, hyp :- (le Real 0 x), ...]
  proposition
  (tactic1 arg1 arg2)
  (tactic2)
  ...)

;; Structure (compiles to defrecord)
(a/structure Point [] (x Nat) (y Nat))
;; Creates: (->Point 3 4) => #user.Point{:x 3, :y 4}
;; Access: (:x p), (:y p)

;; Inductive type
(a/inductive Color [] (red) (green) (blue))
(a/inductive MyList [α Type] (nil) (cons [head α] [tail (MyList α)]))

;; Indexed inductive family (length-indexed vector)
(a/inductive Vec [α Type] :indices [n Nat]
  (nil :where [0])
  (cons [a α] [m Nat] [tail (Vec α m)] :where [(+ m 1)]))
```

### Pattern Matching

```clojure
;; Match on inductive types — uses CIC recursor under the hood
(match expr InductiveType ReturnType
  (ctor1 body1)                          ;; leaf case
  (ctor2 [field1 field2 ...] body2))     ;; node case with field bindings

;; Induction hypotheses are auto-generated for recursive fields:
;;   ih_left, ih_right (named after fields), or ih0, ih1
(a/defn size [t (MyList Nat)] Nat
  (match t (MyList Nat) Nat
    (nil 0)
    (cons [head tail] (+ 1 ih_tail))))
```

### Tactics

| Tactic | Description |
|--------|-------------|
| `(apply lemma_name)` | Apply a lemma, generating subgoals for arguments |
| `(assumption)` | Close goal from local context |
| `(simp "lemma1" "lemma2")` | Simplify using rewrite lemmas |
| `(rfl)` | Close `a = a` goals |
| `(intro)` / `(intros x y)` | Introduce forall binders |
| `(induction n)` | Structural induction |
| `(cases h)` | Case analysis |
| `(omega)` | Linear arithmetic on Nat/Int |
| `(ring)` | Polynomial identity |
| `(linarith)` | Linear arithmetic over ordered fields |
| `(norm_num)` | Numeric normalization |
| `(positivity)` | Prove `0 ≤ expr` goals |
| `(gcongr)` | Generalized congruence |
| `(solve_by_elim)` | Backward chaining from context |
| `(constructor)` | Apply the goal's constructor |
| `(exfalso)` | Prove by contradiction (change goal to False) |
| `(left)` / `(right)` | Choose disjunction branch |
| `(have name type)` | Introduce intermediate lemma |
| `(rewrite h)` | Rewrite goal using hypothesis |
| `(try (tactic))` | Try tactic, ignore failure |
| `(all_goals (tactic))` | Apply to all open goals |
| `(first (tac1) (tac2))` | Try tactics in order |

## Configuration

All limits are configurable via dynamic vars in `ansatz.config`:

```clojure
(require '[ansatz.config :as config])

;; Increase fuel for complex proofs
(binding [config/*high-fuel* 100000000]
  (a/theorem ...))

;; Enable grind debugging
(binding [config/*grind-debug* true]
  (a/theorem ... (grind)))

;; Register custom simplification procedure
(binding [config/*simprocs* [(fn [st expr] ...)]]
  (a/theorem ... (simp)))
```

| Var | Default | Description |
|-----|---------|-------------|
| `*default-fuel*` | 20M | Type checker fuel per operation |
| `*high-fuel*` | 50M | Fuel for deep instance chains |
| `*max-whnf-depth*` | 512 | Maximum WHNF reduction depth |
| `*max-synth-depth*` | 16 | Instance synthesis recursion depth |
| `*max-candidates*` | 32 | Instance candidates tried per class |
| `*max-simp-steps*` | 100k | Maximum simp rewrite steps |
| `*verbose*` | true | Print proof/definition results |
| `*grind-debug*` | false | Log grind tactic exceptions |
| `*simprocs*` | [] | User-registered simplification procedures |

## Extending Ansatz

Ansatz provides three extension points, following Lean 4's metaprogramming model. Extensions have full access to the CIC kernel (`tc/infer-type`, `tc/cached-whnf`, `tc/is-def-eq`) and proof state.

### Custom Tactics (Lean 4's `@[tactic]`)

```clojure
;; Register a tactic that tries rfl, then assumption, then omega
(a/register-tactic! 'auto
  (fn [ps args]
    (or (try (basic/rfl ps) (catch Exception _ nil))
        (try (basic/assumption ps) (catch Exception _ nil))
        (try (omega/omega ps) (catch Exception _ nil)))))

;; Use it in proofs:
(a/theorem foo [n :- Nat] (<= Nat 0 n) (auto))
```

### Custom Elaboration Forms (Lean 4's `elab_rules`)

```clojure
;; Register a custom syntax form that elaborates to kernel Expr
(a/register-elaborator! 'double
  (fn [env scope depth args lctx]
    (let [x (ansatz.core/sexp->ansatz env scope depth (first args) lctx)]
      ;; Build: x + x
      ...)))

;; Use in definitions:
(a/defn f [n :- Nat] Nat (double n))
```

### Custom Simprocs (Lean 4's `@[simproc]`)

```clojure
;; Register a simplification procedure (always active during simp)
(a/register-simproc! 'my-domain/simplify
  (fn [st expr]
    ;; Return {:expr simplified :proof eq-proof} or nil
    nil))
```

See [examples/metaprogramming.clj](examples/metaprogramming.clj) for working examples.

## Development

```bash
# Compile Java kernel (required after changing .java files)
clj -T:build javac

# Run tests
clj -M:test

# Check formatting
clj -M:format

# Fix formatting
clj -M:ffix

# Lint
clj -M:lint

# Start REPL
clj -M:repl
```

See [CLAUDE.md](CLAUDE.md) for detailed developer workflow, REPL navigation, tracing, and verification commands.

## Architecture

```
Lean 4 Mathlib + CSLib  →  lean4export  →  Ansatz PSS store
                                                  ↓
                                          ansatz.core/init!
                                                  ↓
                                          Env (immutable, on-demand loading)
                                                  ↓
                    ┌────────────┬────────────────┴────────────────┐
                    ↓            ↓                                 ↓
             a/defn        a/structure                      a/theorem
             (+ :termination-by)  (→ defrecord)            (prove with tactics)
                    ↓            ↓                                 ↓
             Native JVM fn  Clojure record             Java TypeChecker verifies
```

### Kernel (Java)

The CIC kernel is implemented in Java for performance:
- `TypeChecker` — type inference and definitional equality
- `Reducer` — WHNF reduction (beta, delta, iota, zeta, projection)
- `FlatStore` — memory-mapped expression store for zero-copy lookup
- `Env` — declaration environment with external lookup

For a deeper architectural walkthrough of the kernel, see [doc/kernel.md](doc/kernel.md).

### Tactic Layer (Clojure)

Tactics are pure functions `(proof-state → proof-state)` on immutable Clojure maps. Backtracking is free via persistent data structures (no save/restore needed).

- `basic.clj` — apply, intro, assumption, cases, induction, rewrite
- `simp.clj` — simplification by rewriting (Lean 4's simp architecture)
- `omega.clj` — linear arithmetic for Nat/Int (ground + non-ground goals)
- `instance.clj` — typeclass synthesis with tabled resolution
- `extract.clj` — proof term extraction and verification

### Surface Layer (Clojure)

- `core.clj` — public API (`defn`, `theorem`, `inductive`, `init!`)
- `config.clj` — centralized configuration (fuel, depth, limits)
- S-expression compiler translates Clojure forms to CIC kernel expressions

## Building from Source

```bash
git clone https://github.com/replikativ/ansatz.git
cd ansatz

# Compile Java kernel
clj -T:build javac

# Run tests (requires test-data/init-medium.ndjson)
clj -M:test

# Start REPL
clj -M:repl
```

## Lean 4 Attribution

Ansatz implements the Calculus of Inductive Constructions following [Lean 4](https://github.com/leanprover/lean4) (Apache 2.0). The kernel type checker, reducer, and tactic infrastructure are independent implementations in Java/Clojure, informed by Lean 4's algorithms but without copying source code. Mathlib and CSLib declarations are imported via [lean4export](https://github.com/leanprover/lean4export). [CSLib](https://github.com/leanprover/cslib) (Apache 2.0) provides the verified algorithms library.

## License

Apache License 2.0 — same as Lean 4. See [LICENSE](LICENSE).

Copyright 2026 Christian Weilbach
