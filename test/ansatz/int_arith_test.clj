(ns ansatz.int-arith-test
  "Int is a carrier like any other: numerals take its type, its terms are the ones Lean's own
   lemmas are stated about, the tactics reason about them, and the functions run.

   Each of these failed before: `(+ a 1)` was a type error (a Nat literal under `Int.add`),
   an Int function had no runtime lowering, `omega`/`simp` could not touch a goal stated with
   our `Int.add` spelling, and a numeral in an argument position — `(= Int a 0)` — stayed a
   Nat for every carrier but Nat."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]))

(def ^:private mathlib-store
  ;; Resolved through ansatz.store (never a hardcoded path), and never FETCHED: a test must
  ;; not download 1.3 GiB. Without the store these tests report themselves skipped.
  (delay ((requiring-resolve 'ansatz.store/resolve-existing) "mathlib")))

(defn- with-init [f]
  (if-let [path @mathlib-store]
    (let [saved-env @a/ansatz-env saved-idx @a/ansatz-instance-index]
      (try (binding [a/*verbose* false] (a/init! (str path) "mathlib") (f))
           (finally (reset! a/ansatz-env saved-env)
                    (reset! a/ansatz-instance-index saved-idx))))
    (println "  (skipping int-arith-test — no mathlib store)")))

(use-fixtures :once with-init)

(deftest numerals-take-the-carrier-s-type
  (testing "in arithmetic"
    (a/defn ^Int inc-int [^Int a] (+ a 1))
    (is (= 42 (inc-int 41)))
    (a/defn ^Int dec-int [^Int a] (- a 1))
    (is (= 42 (dec-int 43))))
  (testing "and in any argument position — the numeral is not confined to arithmetic"
    (a/theorem int-eq-zero-refl [a :- Int, h :- (= Int a 0)] (= Int a 0) (assumption))
    (a/theorem real-eq-zero-refl [x :- Real, h :- (= Real x 0)] (= Real x 0) (assumption))))

(deftest int-terms-are-the-ones-mathlib-is-stated-about
  (testing "omega reasons about Int goals"
    (a/theorem int-add-zero-omega [a :- Int] (= Int (+ a 0) a) (omega))
    (a/theorem int-add-comm-omega [a :- Int, b :- Int] (= Int (+ a b) (+ b a)) (omega))
    (a/theorem int-sub-self-omega [a :- Int] (= Int (- a a) 0) (omega)))
  (testing "and simp applies Mathlib's own Int lemmas to them"
    (a/theorem int-add-zero-simp [a :- Int] (= Int (+ a 0) a) (simp [Int.add_zero]))))

(deftest int-functions-run
  (a/defn ^Int poly [^Int a ^Int b] (- (* a b) 1))
  (is (= 41 (poly 6 7)))
  (a/defn ^Int halve [^Int a] (quot a 2))
  (is (= 42 (halve 85)))
  (testing "Nat keeps its own lowering (truncated subtraction, floor division)"
    (a/defn ^Nat nsub [^Nat m ^Nat n] (- m n))
    (is (= 0 (nsub 3 5)) "Nat subtraction truncates at zero")))
