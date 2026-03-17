# Lean 4 for Clojurians

Ansatz brings Lean 4's type theory to Clojure. This guide explains the relationship, how to learn the concepts, and how proofs move between the two systems.

## What Lean 4 Is

[Lean 4](https://lean-lang.org/) is a theorem prover and programming language built on the **Calculus of Inductive Constructions** (CIC) — a type theory where propositions are types and proofs are programs. Its math library [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) has 648,000+ formalized declarations covering algebra, analysis, topology, probability, and more.

Ansatz implements **the same CIC kernel** in Java, verified declaration-by-declaration against Lean 4's export format. A proof verified by Ansatz is valid in Lean 4 and vice versa — they share the same foundations.

## The Key Idea: Types as Specifications

In Clojure, you write tests:
```clojure
(assert (= (+ 2 3) 5))        ;; true for these specific values
```

In Ansatz/Lean 4, you write proofs:
```clojure
(a/theorem add-comm [n :- Nat, m :- Nat]
  (= Nat (+ n m) (+ m n))     ;; true for ALL n and m
  (simp "Nat.add_comm"))
```

The theorem is a *universally quantified* statement checked at compile time by the CIC kernel. The `simp` tactic builds a proof term that the kernel verifies — it's not a runtime assertion, it's a mathematical guarantee.

This is the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence): a type is a proposition, a value of that type is a proof, and type-checking is proof verification.

## Syntax Translation

The concepts are identical — only the surface syntax differs:

### Definitions

```
Lean 4                                    Ansatz
────────────────────────────────────────  ──────────────────────────────────────
def double (n : Nat) : Nat := n + n       (a/defn double [n :- Nat] Nat (+ n n))

theorem add_zero (n : Nat) :              (a/theorem add-zero [n :- Nat]
    n + 0 = n := by                         (= Nat (+ n 0) n)
  simp [Nat.add_zero]                       (simp "Nat.add_zero"))

inductive Color where                     (a/inductive Color []
  | red | green | blue                      (red) (green) (blue))

inductive MyList (α : Type) where         (a/inductive MyList [α Type]
  | nil                                     (nil)
  | cons (head : α) (tail : MyList α)      (cons [head α] [tail (MyList α)]))
```

### Indexed Families

```
Lean 4                                    Ansatz
────────────────────────────────────────  ──────────────────────────────────────
inductive Vec (α : Type) : Nat → Type     (a/inductive Vec [α Type] :indices [n Nat]
  | nil : Vec α 0                           (nil :where [0])
  | cons : α → {n : Nat} →                 (cons [a α] [m Nat]
      Vec α n → Vec α (n + 1)                    [tail (Vec α m)]
                                                  :where [(+ m 1)]))
```

### Tactics

| Lean 4 | Ansatz | What it does |
|--------|--------|-------------|
| `intro h` | `(intro h)` | Name a hypothesis |
| `exact term` | `(apply term)` | Provide exact proof term |
| `assumption` | `(assumption)` | Use hypothesis matching goal |
| `rfl` | `(rfl)` | Reflexivity (`a = a`) |
| `simp [lem]` | `(simp "lem")` | Simplify with rewrite lemmas |
| `omega` | `(omega)` | Linear arithmetic on Nat/Int |
| `ring` | `(ring)` | Polynomial identity |
| `linarith` | `(linarith)` | Linear arithmetic over fields |
| `norm_num` | `(norm_num)` | Numeric normalization |
| `positivity` | `(positivity)` | Prove `0 ≤ expr` |
| `cases h` | `(cases h)` | Case split on inductive |
| `induction n` | `(induction n)` | Structural induction |
| `constructor` | `(constructor)` | Apply goal's constructor |
| `have h : T := p` | `(have h T)` | Introduce intermediate lemma |
| `all_goals tac` | `(all_goals (tac))` | Apply tactic to all goals |
| `first \| t1 \| t2` | `(first (t1) (t2))` | Try tactics in order |

### Pattern Matching

```
Lean 4                                    Ansatz
────────────────────────────────────────  ──────────────────────────────────────
def size : MyList Nat → Nat               (a/defn size [t (MyList Nat)] Nat
  | .nil => 0                               (match t (MyList Nat) Nat
  | .cons _ tail => 1 + size tail             (nil 0)
                                              (cons [head tail] (+ 1 ih_tail))))
```

In Ansatz, `ih_tail` is the induction hypothesis — the recursive result for the `tail` field. Lean 4 handles this via the equation compiler; Ansatz makes it explicit.

## Kernel Compatibility

Both systems implement identical CIC:

| Component | Lean 4 (C++) | Ansatz (Java) | Status |
|-----------|-------------|---------------|--------|
| Expressions | `expr.h` | `Expr.java` | Identical (11 node types) |
| Type checking | `type_checker.cpp` | `TypeChecker.java` | Same algorithm |
| Reduction | `type_checker.cpp` | `Reducer.java` | Same rules (beta/delta/iota/zeta/proj) |
| Universe levels | `level.h` | `Level.java` | Same algebra (max/imax) |
| Proof irrelevance | `is_def_eq` | `isDefEq` | Same semantics |
| Recursor reduction | `reduce_recursor` | `tryReduceRecursor` | Same (K-rec, eta, literals) |

**A proof term `p : Prop` verified in Ansatz will type-check in Lean 4** (and vice versa), provided both reference the same Mathlib declarations.

## Proof Portability

### Lean 4 → Ansatz

All of Mathlib's 648k declarations are imported via [lean4export](https://github.com/leanprover/lean4export) into Ansatz's store. When you write `(apply mul_le_of_le_one_left)` in Ansatz, you're applying a theorem proved in Mathlib and verified by the CIC kernel.

### Ansatz → Lean 4

Ansatz includes a Lean 4 emitter (`ansatz.surface.lean`) that produces fully explicit Lean 4 code. A theorem proved in Ansatz can be exported and verified by Lean 4's kernel.

### What's Different

Ansatz is **not** a Lean 4 frontend — it's a Clojure library that shares Lean 4's kernel. Differences:

- **Elaboration**: Lean 4 has sophisticated implicit argument inference with postponement. Ansatz has simpler elaboration that covers common cases.
- **Notation**: Lean 4 has a powerful custom notation system. Ansatz uses s-expressions.
- **Compilation**: Lean 4 compiles to C (Perceus RC). Ansatz compiles to JVM bytecode.
- **Metaprogramming**: Lean 4 uses typed macros and monadic elaboration. Ansatz uses Clojure macros + open registries (`register-tactic!`, `register-elaborator!`, `register-simproc!`).

## Learning Path

### 1. Understand Tactic Proofs (1-2 hours)

**[Natural Number Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4)** — Browser-based, no installation. Build natural number arithmetic from scratch using tactics. The best way to develop intuition for what `intro`, `rfl`, `rw`, `simp`, and `induction` do.

### 2. Read Lean 4 Proofs (30 minutes)

**[The Hitchhiker's Guide to Reading Lean 4 Theorems](https://blog.lambdaclass.com/the-hitchhikers-guide-to-reading-lean-4-theorems/)** — "If you can read Python or TypeScript, you can learn to read Lean proofs." Explains theorem structure, core tactics, and how to navigate Mathlib.

### 3. Learn the Type Theory (2-4 hours)

**[Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)**, Chapters 2-5:
- Ch 2: Dependent Type Theory — types, functions, universes
- Ch 3: Propositions and Proofs — Curry-Howard
- Ch 4: Quantifiers and Equality — forall, exists, rewriting
- Ch 5: Tactics — interactive proof construction

### 4. Use Mathlib (ongoing)

**[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)** — Interactive tutorial using Mathlib lemmas. Directly applicable to Ansatz since it uses the same declarations.

### 5. Find Lemmas

- **[Loogle](https://loogle.lean-lang.org/)** — Search by name or pattern: `Nat._, _ + _ = _ + _`
- **[Lean Finder](https://leanfinder.github.io/)** — Natural language: "multiplication distributes over addition"
- **[Mathlib API Docs](https://leanprover-community.github.io/mathlib4_docs/)** — Browsable with fuzzy search
- In Ansatz REPL: `(s/find-decl ctx "add_comm")` searches by name substring

### Additional Resources

- **[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)** — Lean as a programming language
- **[The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)** — Gentler mathematical pace
- **[Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/)** — Deep dive into the kernel (relevant to Ansatz internals)
- **[Lean 4 Tactics Cheatsheet (PDF)](https://raw.githubusercontent.com/madvorak/lean4-cheatsheet/main/lean-tactics.pdf)** — Printable reference
- **[Lean Playground](https://live.lean-lang.org/)** — Try Lean 4 in the browser
