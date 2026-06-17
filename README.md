# Ansatz

**Write Clojure. Prove it correct. Run as ordinary JVM code.**

[![Clojars Project](https://img.shields.io/clojars/v/org.replikativ/ansatz.svg)](https://clojars.org/org.replikativ/ansatz)
[![CircleCI](https://circleci.com/gh/replikativ/ansatz.svg?style=shield)](https://circleci.com/gh/replikativ/ansatz)
[![Last Commit](https://img.shields.io/github/last-commit/replikativ/ansatz/main.svg)](https://github.com/replikativ/ansatz/commits/main)

Ansatz is a verified programming library for Clojure built on the [Calculus of Inductive Constructions](https://en.wikipedia.org/wiki/Calculus_of_inductive_constructions) (CIC) — the same type theory that powers [Lean 4](https://lean-lang.org/). It implements Lean 4's kernel in Java, type-checks proofs against [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) (210k+ theorems, 648k declarations) and [CSLib](https://github.com/leanprover/cslib) (verified algorithms), and compiles verified functions to ordinary Clojure/JVM code.

If you already write [malli](https://github.com/metosin/malli)-instrumented Clojure, Ansatz is the gradual next step: your `m/=>` schemas become kernel type signatures, your functions become machine-checked, and they still run as ordinary Clojure.

**Same kernel, different surface.** Ansatz shares Lean 4's CIC kernel — a proof verified in Ansatz is valid in Lean 4 and vice versa. Proofs can be [exported to Lean 4](doc/lean4-for-clojurians.md) syntax. The difference is the surface language: Lean 4 uses its own syntax; Ansatz uses Clojure s-expressions and runs on the JVM. See **[Lean 4 for Clojurians](doc/lean4-for-clojurians.md)** for the full comparison, translation guide, and learning path.

```clojure
(require '[ansatz.core :as a] '[malli.core :as m])
(a/load-init!)   ;; zero-config: the Lean Init environment bundled in the jar

;; The gradual on-ramp: keep your malli schema, change defn → a/defn.
;; The schema becomes the kernel type; the function is machine-checked and
;; still compiles to an ordinary Clojure fn.
(m/=> add2 [:=> [:cat :int :int] :int])
(a/defn add2 [x y]
  (match x Nat Nat (zero y) (succ [k] (+ 1 (add2 k y)))))
(add2 20 22) ;; => 42

;; [:map …] schemas become named-field records: keyword access is kernel-verified,
;; runtime values stay plain Clojure maps
(m/=> dot [:=> [:cat [:map [:x :int] [:y :int]]] :int])
(a/defn dot [p] (+ (:x p) (:y p)))
(dot {:x 2 :y 3}) ;; => 5

;; refinements: an [:int {:min 1}] param carries its bound as a Prop in the kernel
;; type (a Subtype) — and is still used directly as a number in the body
(m/=> pred [:=> [:cat [:int {:min 1}]] :int])
(a/defn pred [n] (- n 1))

;; the differential check: compiled runtime ≡ kernel evaluation on schema-generated
;; inputs — catches elaboration bugs that are well-typed but unfaithful to the source
(require '[ansatz.malli :as am])
(am/check-verified! 'my.ns 'add2 :runs 25) ;; => {:runs 25 :ok 25}
```

Beyond schemas, full CIC types — here is verified merge, where the kernel *proves
termination* (a lexicographic `sizeOf` measure, guessed automatically and embedded
in the kernel term):

```clojure
(a/defn merge [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (match xs (List Nat) (List Nat)
    (nil ys)
    (cons [x xs']
      (match ys (List Nat) (List Nat)
        (nil (cons x xs'))
        (cons [y ys']
          (if (<= x y)
            (cons x (merge xs' (cons y ys')))
            (cons y (merge (cons x xs') ys'))))))))
;; explicit spellings also work:
;;   :termination-by (+ (sizeOf xs) (sizeOf ys))   or   [(sizeOf xs) (sizeOf ys)]

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
(a/defn rb-size [t :- (RBTree Nat)] Nat
  (match t (RBTree Nat) Nat
    (leaf 0)
    (node [color left key right] (+ 1 (+ ih_left ih_right)))))

;; Nested match for BST lookup — references outer param k
(a/defn rb-member [t :- (RBTree Nat), k :- Nat] Bool
  (match t (RBTree Nat) Bool
    (leaf false)
    (node [color left key right]
      (match (< k key) Bool Bool
        (true ih_left)                    ;; recurse into left subtree
        (false (match (== k key) Bool Bool
                 (true true)              ;; found it
                 (false ih_right)))))))   ;; recurse into right subtree

;; A verified constant (constructors are ordinary constants in term position)
(a/defn tree [] (RBTree Nat)
  (RBTree.node Nat RBColor.black
    (RBTree.node Nat RBColor.red (RBTree.leaf Nat) 2 (RBTree.leaf Nat))
    4
    (RBTree.node Nat RBColor.red (RBTree.leaf Nat) 6 (RBTree.leaf Nat))))

;; All verified functions compile to ordinary Clojure and run on the JVM
(rb-size tree)           ;; => 3
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

;; The following proofs use definitions from examples/ (llen, lmap, Sorted,
;; insertSorted, balance1, ValidRB — see verified_list.clj, sorting.clj, rbtree.clj).

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
- **Malli schemas as signatures (optional)** — the gradual-typing on-ramp: keep your `(m/=> f [:=> [:cat :int :int] :int])` declarations and change `defn` to `a/defn`; the schema becomes the kernel signature. Collections→`List`; `[:map [:x :int] …]`→a synthesized named-field record (keyword access `(:x p)` elaborates to kernel projections, runtime values stay plain Clojure maps); `[:int {:min k}]`→`Subtype` refinements whose params are still usable directly as numbers (references auto-coerce to `.val`, the refinement stays in the binder for proofs). `ansatz.malli/check-verified!` adds a generative differential check — schema-generated inputs run through both the compiled runtime and the kernel evaluator and must agree, guarding the well-typed-but-unfaithful elaboration bug class the kernel can't see. malli loads lazily; core has no hard dependency
- **Grind tactic** — automated reasoning via persistent E-graph with congruence closure, propositional propagators (And/Or/Not/Eq/ite), E-matching for lemma instantiation, constructor injection/discrimination, and theory solver integration
- **Kernel-enforced termination** — every recursive definition carries its termination proof in the kernel term: structural recursion, `:termination-by` measures (scalar, **lexicographic** `[m n]` — Ackermann verifies, `(sizeOf xs)` over data structures), automatic measure guessing, and `loop`/`recur`; non-terminating definitions are rejected with actionable errors (`^:partial` is the explicit trusted escape)
- **One lean4-shaped elaborator** — fvar/metavar elaboration with implicit + universe inference for bodies, signatures, measures, theorem statements, and tactic arguments; Clojure macros (`->`, `when`, `and`/`or`, yours) expand by default and compose
- **Structures** — `a/structure` compiles to `defrecord` with keyword access and pretty-printing
- **Generic types** — implicit type parameter inference via auto-elaborate (polymorphic constructors work without explicit type annotations)
- **Lean 4 Mathlib + CSLib** — 648k Mathlib declarations + CSLib verified algorithms
- **Tactic proofs** — `apply`, `simp`, `omega`, `ring`, `grind`, `assumption`, `induction`, `cases`, and more
- **Instance synthesis** — automatic typeclass resolution with tabled backtracking
- **Compiled output** — verified `defn` compiles to ordinary Clojure `fn` with arity-aware flat calls
- **Extensible** — `register-elaborator!` is lean4 `macro_rules`-shaped (your fn maps argument forms to a replacement surface form, the elaborator does the rest); plus custom tactics and simprocs with full kernel access
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

This clones `lean4export` and `mathlib4` (if not present), exports Mathlib to NDJSON
with `mdata` preserved,
generates the instance registry, and imports into an Ansatz store under the durable
store root (`$ANSATZ_STORE_DIR` → `$XDG_DATA_HOME/ansatz/stores` → `~/.local/share/ansatz/stores`;
pass an explicit directory as the first argument to override). Takes ~20 minutes on first run.
Avoid `/tmp`/`/var/tmp` for stores — `systemd-tmpfiles` erodes them; pre-existing legacy
stores at `/var/tmp/ansatz-<name>` are still found automatically when loading.

To re-check an imported store through the kernel:

```bash
clj -M -e '
(require (quote [ansatz.export.storage :as s]))
(let [store (s/open-store ((requiring-resolve (quote ansatz.store/resolve-existing)) "mathlib"))]
  (try
    (prn (s/verify-from-store! store "mathlib"
                               :verbose? true
                               :timeout-ms 300000))
    (finally
      (s/close-store store))))
'
```

The authoritative full-corpus check uses the PSS-backed store. The imported-store
verifier uses a higher fuel default than interactive tactic calls because full
Mathlib contains legitimate declarations above 20M kernel steps. For trace-level
comparison against a patched Lean 4 build, see
[doc/kernel-validation.md](doc/kernel-validation.md).

**Manual setup**

If you prefer step-by-step:

```bash
# 1. Clone and build lean4export (https://github.com/leanprover/lean4export)
git clone https://github.com/leanprover/lean4export.git ../lean4export
cd ../lean4export && lake build

# 2. Export Mathlib to NDJSON (~5 min, ~5GB)
# Preserve mdata so imported declarations stay closer to Lean kernel trace space.
cd ../mathlib4
lake env ../lean4export/.lake/build/bin/lean4export --export-mdata Mathlib > ../ansatz/test-data/mathlib.ndjson

# 3. Generate instance registry from Mathlib (~2 min)
lake env lean DumpInstances.lean   # produces instances.tsv
cp instances.tsv ../ansatz/resources/instances.tsv

# 4. Import into Ansatz store (~15 min)
cd ../ansatz
clj -M -e '
(require (quote [ansatz.export.storage :as s]))
(def store (s/open-store ((requiring-resolve (quote ansatz.store/store-dir)) "mathlib")))
(s/import-ndjson-streaming! store "test-data/mathlib.ndjson" "mathlib" :verbose? true)
'
```

### Setup CSLib Store (Verified Algorithms)

[CSLib](https://github.com/leanprover/cslib) is the official Computer Science library for Lean 4 — verified sorting, automata, lambda calculus, and more.

```bash
./scripts/setup-cslib.sh
```

This imports CSLib (including its Mathlib dependency) into a store named `cslib` under the
durable store root (see above).

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

;; Load the Mathlib environment by store name — resolved from the durable store
;; root, falling back to legacy /var/tmp/ansatz-mathlib if that is where it lives.
;; (An explicit path still works: (a/init! "/path/to/store" "mathlib").)
(a/init! "mathlib")

;; Define and prove
(a/defn ^Nat double [^Nat n] (+ n n))

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
;; Binder syntax: ONE grammar, three spellings. parse-params reads the vector as
;; name/type pairs; `:-` separators are optional sugar over the pairs; metadata
;; types are the third skin and keep the vector a plain Clojure binding vector
;; (this is what the malli on-ramp generates). Pick one and stay consistent —
;; this README uses the `:-` spelling with the return type after the vector.
(a/defn add [x :- Nat, y :- Nat] Nat body)   ;; recommended (matches a/theorem binders)
(a/defn add [x Nat, y Nat] Nat body)         ;; bare pairs — same grammar, no separators
(a/defn ^Nat add [^Nat x ^Nat y] body)       ;; metadata types, return type on the name

;; Well-founded recursion — the decrease proof is kernel-checked, not trusted
(a/defn ^Nat fact [^Nat n]
  :termination-by n
  (if (== n 0) 1 (* n (fact (- n 1)))))

;; Lexicographic measures (vector) — Ackermann verifies; the measure is also auto-guessed
(a/defn ^Nat ack [^Nat m ^Nat n]
  :termination-by [m n]
  (match m Nat Nat
    (zero (+ n 1))
    (succ [k] (match n Nat Nat (zero (ack k 1)) (succ [j] (ack k (ack (Nat.succ k) j)))))))

;; Recursion over data structures — sizeOf measures (auto-guessed for List/custom inductives)
(a/defn ^Nat pairs [^{:- (List Nat)} xs]                ; recurses on rest-of-rest
  (match xs (List Nat) Nat
    (nil 0)
    (cons [h t] (match t (List Nat) Nat (nil 0) (cons [h2 t2] (+ 1 (pairs t2)))))))

;; Malli schemas as signatures (optional dep): defn → a/defn, schema unchanged
(m/=> add2 [:=> [:cat :int :int] :int])
(a/defn add2 [x y]
  (match x Nat Nat (zero y) (succ [k] (+ 1 (add2 k y)))))
;; [:map …] schemas become named-field records: keyword access verifies, runtime = plain maps
(m/=> dot [:=> [:cat [:map [:x :int] [:y :int]]] :int])
(a/defn dot [p] (+ (:x p) (:y p)))                       ; (dot {:x 2 :y 3}) => 5
;; refined params are used directly as their carrier ([:int {:min 1}] → Subtype, auto-.val)
;; differential check: compiled runtime ≡ kernel evaluation on generated inputs
(ansatz.malli/check-verified! 'my.ns 'add2 :runs 25)     ; => {:runs 25 :ok 25}

;; loop/recur — hoisted to a verified helper, termination auto-proved
(a/defn ^Nat sum-to [^Nat n]
  (loop [acc 0 i n] (if (== i 0) acc (recur (+ acc i) (- i 1)))))

;; Typeclass params
(a/defn ^{:- (List α)} sort [^{:- Type} α ^:inst ^{:- (Ord α)} inst ^{:- (List α)} xs] ...)

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
(a/defn size [t :- (MyList Nat)] Nat
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
| `*default-fuel*` | 20M | Interactive tactic/typechecker fuel per operation |
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
;; lean4 macro_rules-shaped: the registered fn maps the argument FORMS to a
;; replacement surface form; the elaborator then elaborates the result — so
;; extensions compose with every other surface feature (types, matches, macros).
(a/register-elaborator! 'double
  (fn [args] (list '+ (first args) (first args))))

;; Use in definitions:
(a/defn ^Nat f [^Nat n] (double n))   ;; (f 5) => 10
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
- `InductiveBundleChecker` — Lean-shaped bundled inductive admission, including nested-inductive lowering/restoration
- `RecursorGenerator` — Lean-shaped recursor type and iota-rule generation for imported and frontend-authored inductive bundles
- `Env` — immutable declaration environment with staged external lookup for imported-store verification

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
