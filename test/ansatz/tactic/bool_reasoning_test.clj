(ns ansatz.tactic.bool-reasoning-test
  "Boolean-returning functions must be provable.

   They were not. A Clojure `defn` returning `Bool` — the natural shape for a predicate —
   could not be reasoned about at all, for three compounding reasons, one per layer:

     surface  Clojure's `and`/`or` are MACROS. They expand to `(let [x c] (if x x d))`,
              which elaborates to a `Bool.rec` tree with the discriminant duplicated into a
              branch. Lean's `&&`/`||` are the FUNCTIONS `Bool.and`/`Bool.or`, and every
              Boolean simp lemma is stated about those applications — none of them can match
              a raw `Bool.rec` tree, so simp structurally unfolded it instead, and nesting
              multiplied the unfolding.

     store    the bundled Init tier carried `Bool.and_eq_true` and nothing from the `or`
              half. `(a && b) = true` split into a conjunction; `(a || b) = true` did not
              split at all. `ansatz.attrs` drops names absent from the store without a word,
              so this was invisible.

     tactic   a Bool goal `e = false` (or `e₁ = e₂`) has no propositional structure, and the
              entire Boolean simp set is stated about `_ = true`. Nothing could get a handle
              on the goal — the same content stated as a Prop proved in milliseconds.

   The two theorems in the first deftest are the motivating case: `lexgt` is a lexicographic
   height/round/step comparison, and the two properties are what make a consensus validator
   non-slashable — at most one prevote and one precommit per height/round."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]))

(defn- fresh-init! []
  (binding [a/*verbose* false] (a/load-init!)))

(deftest boolean-predicates-are-provable
  (fresh-init!)
  (a/defn lexgt [h1 Nat, r1 Nat, s1 Nat, h2 Nat, r2 Nat, s2 Nat] Bool
    (or (< h2 h1)
        (and (== h1 h2)
             (or (< r2 r1)
                 (and (== r1 r2) (< s2 s1))))))
  (is (a/has-constant? "lexgt") "the predicate itself compiles and kernel-checks")

  (testing "no-double-sign: a validator never outranks itself"
    (a/theorem no-double-sign [h :- Nat, r :- Nat, s :- Nat]
               (= Bool (lexgt h r s h r s) false)
               (grind))
    (is (a/has-constant? "no-double-sign")))

  (testing "same-round-requires-later-step: at equal height and round it is the step"
    (a/theorem same-round-requires-later-step [h :- Nat, r :- Nat, x :- Nat, y :- Nat]
               (= Bool (lexgt h r x h r y) (< y x))
               (grind))
    (is (a/has-constant? "same-round-requires-later-step"))))

(deftest bool-atoms-and-combinators
  (fresh-init!)

  (testing "a single comparison: `= false` needs the Bool→Prop goal bridge"
    (a/defn bgt [a Nat, b Nat] Bool (< b a))
    (a/theorem bgt-irrefl [a :- Nat] (= Bool (bgt a a) false) (grind bgt))
    (is (a/has-constant? "bgt-irrefl")))

  (testing "an `if` over a comparison (elaborates to dite) — needs the ite/dite simp set"
    (a/defn bge [a Nat, b Nat] Bool (if (< b a) true (== a b)))
    (a/theorem bge-refl [a :- Nat] (= Bool (bge a a) true) (grind bge))
    (is (a/has-constant? "bge-refl")))

  (testing "`or` of two comparisons"
    (a/defn bge2 [a Nat, b Nat] Bool (or (< b a) (== a b)))
    (a/theorem bge2-refl [a :- Nat] (= Bool (bge2 a a) true) (grind bge2))
    (is (a/has-constant? "bge2-refl")))

  (testing "the Bool algebra itself — `or` is the half the store used to be missing"
    (a/theorem or-idem [p :- Bool] (= Bool (or p p) p) (grind))
    (is (a/has-constant? "or-idem"))
    (a/theorem or-absorb [p :- Bool] (= Bool (or p false) p) (grind))
    (is (a/has-constant? "or-absorb"))
    (a/theorem and-absorb [p :- Bool] (= Bool (and p true) p) (grind))
    (is (a/has-constant? "and-absorb"))))

(deftest and-or-elaborate-to-the-lean-functions
  (fresh-init!)
  (testing "(and)/(or) with 0 and 1 argument keep Clojure's meaning"
    (a/defn nullary-and [] Bool (and))
    (a/defn nullary-or [] Bool (or))
    (a/defn unary-or [p Bool] Bool (or p))
    (a/theorem nullary-and-true [] (= Bool (nullary-and) true) (rfl))
    (a/theorem nullary-or-false [] (= Bool (nullary-or) false) (rfl))
    (a/theorem unary-or-id [p :- Bool] (= Bool (unary-or p) p) (rfl))
    (is (a/has-constant? "nullary-and-true"))
    (is (a/has-constant? "nullary-or-false"))
    (is (a/has-constant? "unary-or-id"))))
