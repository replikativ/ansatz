(ns ansatz.theory.inferred-real-test
  "The inferred surface forms over Real, against the Mathlib store: the README's and
   CLAUDE.md's gradient-descent statements, written without a type the operands carry."
  (:require [clojure.test :refer [deftest is use-fixtures]]
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
    (println "  (skipping inferred-real-test — no mathlib store)")))

(use-fixtures :once with-init)

(deftest real-statements-without-types
  (a/theorem ir-kappa-nonneg [η :- Real, L :- Real, hη :- (<= 0 η), hb :- (<= (* η L) 1)]
             (<= 0 (- 1 (* η L)))
             (apply sub_nonneg_of_le) (assumption))
  (a/theorem ir-numerals [] (<= (+ 1 1) 3) (norm_num))
  (is true))

(deftest real-gd-step-and-rate
  (a/defn ^{:- Real} ir-gd-step [^{:- Real} x ^{:- Real} grad ^{:- Real} eta]
    (- x (* eta grad)))
  (a/theorem ir-gd-rate [κ :- Real, ε₀ :- Real, n :- Nat,
                         hκ₀ :- (<= 0 κ), hκ₁ :- (<= κ 1), hε₀ :- (<= 0 ε₀)]
             (<= (* (pow κ n) ε₀) ε₀)
             (apply mul_le_of_le_one_left) (assumption)
             (apply pow_le_one₀) (all_goals (assumption)))
  (is true))
