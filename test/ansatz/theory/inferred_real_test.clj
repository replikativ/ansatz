(ns ansatz.theory.inferred-real-test
  "The inferred surface forms over Real, against the Mathlib store: the README's and
   CLAUDE.md's gradient-descent statements, written without a type the operands carry."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]))

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

(deftest real-double-profile-requires-standard-instances
  (let [en (a/env)
        c (fn [s]
            (let [nm (name/from-string s) ci (env/lookup en nm)]
              (e/const' nm (repeat (alength (.levelParams ^ansatz.kernel.ConstantInfo ci)) level/zero))))
        real (c "Real") nat (c "Nat")
        lower (fn [op beta instance]
                (eval (cg/ansatz->clj
                       en (e/lam "x" real
                                 (e/lam "y" beta
                                        (e/app* (c op) real beta real instance
                                                (e/bvar 1) (e/bvar 0)) :default) :default) [])))]
    (doseq [[op beta dict x y expected]
            [["HAdd.hAdd" real (e/app* (c "instHAdd") real (c "Real.instAdd")) 5.0 2.0 7.0]
             ["HMul.hMul" real (e/app* (c "instHMul") real (c "Real.instMul")) 5.0 2.0 10.0]
             ["HSub.hSub" real (e/app* (c "instHSub") real (c "Real.instSub")) 5.0 2.0 3.0]
             ["HDiv.hDiv" real (e/app* (c "instHDiv") real
                                       (e/app* (c "DivInvMonoid.toDiv") real (c "Real.instDivInvMonoid")))
              5.0 2.0 2.5]
             ["HPow.hPow" nat (e/app* (c "instHPow") real nat
                                      (e/app* (c "NPow.toPow") real
                                              (e/app* (c "Monoid.toNPow") real (c "Real.instMonoid"))))
              5.0 2 25.0]
             ["HPow.hPow" real (e/app* (c "instHPow") real real (c "Real.instPow")) 5.0 2.0 25.0]]]
      (is (= expected (((lower op beta dict) x) y)) [op :standard])
      (let [cls (subs op 0 (.indexOf ^String op "."))
            identity-op (e/lam "x" real (e/lam "y" beta (e/bvar 1) :default) :default)
            custom (e/app* (c (str cls ".mk")) real beta real identity-op)]
        (is (= x (((lower op beta custom) x) y)) [op :custom])))))
