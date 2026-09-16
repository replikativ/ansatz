(ns ansatz.tactic.carriers-test
  "The arithmetic tactics on carriers other than Nat, against the Mathlib store.

   What each pins, and what failed before:
   - `decide` and simp synthesize against Lean's @[instance] registry, not name-guessing, so
     `Nat.decLe` is found for `(2 : Nat) ≤ 3` (norm_num reported \"no instance found\").
   - Instance selection keys two levels deep and ignores mdata, so a `Decidable` instance
     for a Nat relation is not lost among the 80 `LE.le` instances of other carriers.
   - `norm_num` proves numeral order over an ordered semiring with no Decidable instance
     (Real) by Mathlib's `isNat_le_true`/`isNat_lt_true` — its Ineq extension, isNat case.
   - `omega` treats a relation over a carrier it does not handle as no fact, as Lean's
     frontend does, instead of reifying it as Int and returning an ill-typed proof; so
     `positivity`, which tries omega first, falls through to its own lemmas."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]))

(def ^:private mathlib-store
  (delay ((requiring-resolve 'ansatz.store/resolve-existing) "mathlib")))

(defn- with-init [f]
  (if-let [path @mathlib-store]
    (let [saved-env @a/ansatz-env saved-idx @a/ansatz-instance-index]
      (try (binding [a/*verbose* false]
             (a/init! (str path) "mathlib")
             (f))
           (finally (reset! a/ansatz-env saved-env)
                    (reset! a/ansatz-instance-index saved-idx))))
    (println "  (skipping carriers-test — no mathlib store)")))

(use-fixtures :once with-init)

(deftest decidable-relations-resolve-through-the-registry
  (a/theorem nat-le-decide [] (<= Nat 2 3) (decide))
  (a/theorem nat-le-norm-num [] (<= Nat 2 3) (norm_num))
  (a/theorem int-le-norm-num [] (<= Int 2 3) (norm_num))
  (a/theorem int-numeral-sum [] (= Int (+ 2 2) 4) (norm_num))
  (is true))

(deftest norm-num-orders-numerals-of-an-ordered-semiring
  (testing "no Decidable instance exists for Real's order; Mathlib's isNat_le_true does it"
    (a/theorem real-le [] (<= Real 1 2) (norm_num))
    (a/theorem real-lt [] (< Real 1 2) (norm_num))
    (a/theorem real-ge [] (>= Real 5 2) (norm_num))
    (a/theorem real-zero-one [] (<= Real 0 1) (norm_num)))
  (testing "and a false comparison stays unproven"
    (is (thrown? Exception (a/theorem real-false [] (<= Real 3 2) (norm_num))))))

(deftest omega-handles-nat-and-int-only
  (a/theorem omega-nat [n :- Nat] (<= Nat n (+ n 1)) (omega))
  (a/theorem omega-int [a :- Int] (<= Int a (+ a 1)) (omega))
  (testing "a Real hypothesis is ignored, not reified"
    (a/theorem omega-ignores-real [n :- Nat, x :- Real, h :- (<= Real x 1)] (<= Nat n (+ n 1)) (omega)))
  (testing "a Real goal is refused cleanly — never an ill-typed proof"
    (is (thrown-with-msg? Exception #"omega" (a/theorem omega-real [] (<= Real 1 2) (omega))))))

(deftest positivity-falls-through-past-omega
  (a/theorem positivity-real-numerals [] (<= Real 1 2) (positivity))
  (is true))
