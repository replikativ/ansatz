# Tutorial: Verified Programming in Clojure

This tutorial teaches you how to write verified Clojure code with Ansatz. No theorem proving or Lean 4 experience needed — just Clojure.

By the end you'll understand:
- How `a/defn` differs from `defn` (and why the difference matters)
- What the kernel actually checks
- How to prove properties about your code
- How `grind` automates most proofs

## Setup

```clojure
(require '[ansatz.core :as a])

;; For this tutorial, init-medium is enough (ships with the repo, no Lean needed):
(a/init! "test-data/init-medium.ndjson")

;; Or with full Mathlib (648k theorems):
;; (a/init! "/var/tmp/ansatz-mathlib" "mathlib")
```

## 1. Your First Verified Function

```clojure
;; Regular Clojure:
(defn double [n] (+ n n))

;; Verified Clojure:
(a/defn double [n Nat] Nat (+ n n))
```

The difference: `a/defn` takes type annotations. `[n Nat]` means n is a natural number. The return type `Nat` comes after the params. The kernel checks that `(+ n n)` actually produces a `Nat` when given a `Nat`.

The result is a normal Clojure function:

```clojure
(double 21) ;; => 42
```

**What happens under the hood:**

Your code `(+ n n)` compiles to a CIC expression:
```
λ (n : Nat) => HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) n n
```

That looks complex, but it's just `n + n` with all the implicit plumbing made explicit:
- `HAdd.hAdd` is the generic `+` operator
- `Nat Nat Nat` are the operand and result types
- `instHAdd Nat instAddNat` is the typeclass instance proving Nat supports addition
- `n n` are your two operands

You wrote `(+ n n)`. Ansatz figured out the rest.

## 2. Pattern Matching

Lists are the bread and butter of Clojure. In Ansatz, `List Nat` is a verified list of natural numbers with two constructors: `nil` (empty) and `cons` (head + tail).

```clojure
;; Length of a list
(a/defn len [l (List Nat)] Nat
  (match l (List Nat) Nat
    (nil 0)
    (cons [hd tl] (+ 1 ih_tail))))
```

The `match` expression does structural recursion on `l`:
- If `l` is `nil` → return 0
- If `l` is `cons hd tl` → return `1 + ih_tail`

**What's `ih_tail`?** It's the *induction hypothesis* — the result of calling `len` recursively on `tl`. The kernel provides it automatically because `tl` is a structural subterm of `l`. You don't write the recursive call explicitly — the kernel guarantees termination.

This compiles to a `List.rec` application (the *recursor* — the only way to eliminate a `List` in CIC). The recursor is what makes termination checking possible.

```clojure
(len '(1 2 3)) ;; => 3
```

More examples:

```clojure
;; Append two lists
(a/defn app [xs (List Nat) ys (List Nat)] (List Nat)
  (match xs (List Nat) (List Nat)
    (nil ys)
    (cons [hd tl] (cons hd ih_tail))))

(app '(1 2) '(3 4)) ;; => (1 2 3 4)

;; Map a function over a list
(a/defn lmap [f (arrow Nat Nat) l (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl] (cons (f hd) ih_tail))))

(lmap inc '(1 2 3)) ;; => (2 3 4)
```

## 3. Equation Theorems

When you define a function with `match`, Ansatz automatically generates *equation theorems* — one per branch:

```
len.eq_1 : len []       = 0
len.eq_2 : len (x::xs)  = 1 + len xs
```

These say: "calling `len` on nil gives 0" and "calling `len` on cons gives 1 + recursive result." They're the key to proving things about `len` — tactics like `simp` and `grind` use them to unfold the function one step at a time.

Why one step? Because if you unfold everything at once, `+` would expand into kernel internals (`Nat.brecOn`, `PProd`...) and become unreadable. The equation theorems keep things clean.

## 4. Your First Proof

A *theorem* states a property and proves it:

```clojure
(a/theorem len-nil []
  (= Nat (len nil) 0)
  (rfl))
```

Reading this:
- **Name**: `len-nil`
- **Parameters**: none (`[]`)
- **Statement**: `len nil = 0` (equality of Nat values)
- **Proof**: `(rfl)` — "reflexivity"

`(rfl)` works when both sides of the `=` reduce to the same value. The kernel computes `len nil`:
1. Unfold `len` → it's a `List.rec` application
2. `List.rec` on `nil` → selects the nil branch → `0`
3. Both sides are `0` ✓

Here's another:

```clojure
(a/theorem app-nil [ys :- (List Nat)]
  (= (List Nat) (app nil ys) ys)
  (rfl))
```

`app nil ys` reduces to `ys` by definition (the nil branch returns `ys`). Both sides are equal → `rfl`.

**But this fails:**

```clojure
;; This does NOT work with rfl:
(a/theorem app-nil-right [xs :- (List Nat)]
  (= (List Nat) (app xs nil) xs)
  (rfl))  ;; ERROR!
```

Why? Because `xs` is a *variable*. The kernel can't reduce `app xs nil` — it doesn't know if `xs` is nil or cons. We need **induction**.

## 5. Induction

Induction splits a goal into cases based on the structure of a value:

```clojure
(a/theorem app-nil-right [xs :- (List Nat)]
  (= (List Nat) (app xs nil) xs)
  (induction xs)
  (all_goals (try (simp_all "app")))
  (all_goals (try (grind "app"))))
```

`(induction xs)` creates two goals:

**Goal 1 (nil):** `app nil nil = nil`
- Both sides reduce to `nil` → closed by simp

**Goal 2 (cons):** `app (hd::tl) nil = hd::tl`
- With IH: `app tl nil = tl`
- `simp "app"` unfolds one step: `app (hd::tl) nil → cons hd (app tl nil)`
- Goal becomes: `cons hd (app tl nil) = cons hd tl`
- The IH says `app tl nil = tl`
- By congruence: `cons hd X = cons hd Y` when `X = Y` → done!

`(all_goals ...)` applies a tactic to every open goal. `(try ...)` means "if this tactic fails, skip it." This pattern — `(induction x) (all_goals (grind "defn"))` — handles most list properties.

## 6. The Grind Tactic

`grind` is the automated reasoning tactic. It combines several strategies:

```clojure
;; Map preserves length (grind handles everything after induction)
(a/theorem map-len [f :- (arrow Nat Nat), l :- (List Nat)]
  (= Nat (len (lmap f l)) (len l))
  (induction l) (all_goals (grind "lmap" "len")))
```

What grind does for the cons case:
1. **Simp**: unfolds `lmap.eq_2` and `len.eq_2` to get `1 + len(lmap f tl) = 1 + len tl`
2. **E-graph**: internalizes all terms and the IH (`len(lmap f tl) = len tl`)
3. **Congruence closure**: `X = Y` implies `1 + X = 1 + Y` → goal closed

The string arguments `"lmap" "len"` tell grind which equation theorems to use. In Lean 4 this is `by grind [lmap, len]`.

More properties grind handles:

```clojure
;; Append is associative
(a/theorem app-assoc [xs :- (List Nat), ys :- (List Nat), zs :- (List Nat)]
  (= (List Nat) (app (app xs ys) zs) (app xs (app ys zs)))
  (induction xs) (all_goals (grind "app")))

;; Map distributes over append
(a/theorem map-app [f :- (arrow Nat Nat), xs :- (List Nat), ys :- (List Nat)]
  (= (List Nat) (lmap f (app xs ys)) (app (lmap f xs) (lmap f ys)))
  (induction xs) (all_goals (grind "lmap" "app")))

;; Append length = sum of lengths
(a/theorem app-len [xs :- (List Nat), ys :- (List Nat)]
  (= Nat (len (app xs ys)) (+ (len xs) (len ys)))
  (induction xs)
  (all_goals (try (simp_all "app" "len" "Nat.add_assoc")))
  (all_goals (try (grind "app" "len"))))
```

The pattern is always: **induction** to split cases, **grind** to close each one.

## 7. Constructor Properties

Grind also handles constructor discrimination (different constructors can't be equal) and injection (same constructor implies equal fields):

```clojure
;; nil and cons are different
(a/theorem cons-ne-nil [x :- Nat, xs :- (List Nat),
                         h :- (= (List Nat) (cons x xs) nil)]
  False
  (grind))

;; Same constructor → same fields
(a/theorem cons-inj [a :- Nat, b :- Nat, xs :- (List Nat), ys :- (List Nat),
                      h :- (= (List Nat) (cons a xs) (cons b ys))]
  (= Nat a b)
  (grind))
```

These work because the kernel knows that `List` has exactly two constructors (`nil` and `cons`), and constructors are injective.

## 8. Custom Types

You can define your own algebraic data types:

```clojure
(a/inductive Color [] (red) (green) (blue))

(a/inductive Tree [α Type]
  (leaf)
  (node [left (Tree α)] [val α] [right (Tree α)]))
```

Type parameters (like `α` in `Tree`) are automatically inferred:

```clojure
;; No need to write (Tree.node Nat ...) — α is inferred from val
(a/defn tree-sum [t (Tree Nat)] Nat
  (match t (Tree Nat) Nat
    (leaf 0)
    (node [l v r] (+ v (+ ih_left ih_right)))))
```

Structures compile to Clojure records:

```clojure
(a/structure Point [] (x Nat) (y Nat))

(let [p (->Point 3 4)]
  (println (:x p) (:y p)))  ;; => 3 4
```

## 9. What Gets Checked?

Every `a/defn` and `a/theorem` goes through the same pipeline:

1. **Compile**: your s-expression → CIC expression tree
2. **Type-check**: the Java kernel infers the type and verifies it matches
3. **Extract** (theorems): build a proof term from tactic steps
4. **Verify** (theorems): the kernel independently checks the proof term
5. **Add to environment**: the definition/theorem becomes available
6. **Compile to Clojure** (functions): generate a normal `fn` for runtime use

The kernel is the *independent arbiter*. Tactics can be buggy, the surface syntax can have quirks, but if the kernel accepts the proof term, the theorem is valid. This is the same trust model as Lean 4 — and since we use the same type theory (CIC), a proof verified in Ansatz is valid in Lean 4 and vice versa.

## 10. What's Next?

- **[examples/verified_list.clj](../examples/verified_list.clj)** — a complete verified list library with 10+ proved properties
- **[examples/rbtree.clj](../examples/rbtree.clj)** — red-black tree with balance invariant proof
- **[examples/sorting.clj](../examples/sorting.clj)** — verified merge sort with well-founded recursion

For the theory behind all this:
- **[Lean 4 for Clojurians](lean4-for-clojurians.md)** — translation guide between Lean 4 and Ansatz syntax
- **[Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)** — the concepts are the same, only the syntax differs
- **[Natural Number Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4)** — interactive tutorial for learning induction proofs (in Lean 4 syntax, but the ideas transfer directly)
