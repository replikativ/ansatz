(ns ansatz.tactic.instance-mathlib-test
  "Instance synthesis over Mathlib's ordered fields follows Lean's tryResolve: a candidate's
   binders become metavariables, its conclusion is unified with the goal, and an implicit class
   binder that the conclusion mentions only under projections (`{inst : Semiring R}` in
   `IsStrictOrderedRing.toPosMulStrictMono`, reached as `Distrib.toMul R (instDistribOfSemiring R
   inst)`) is synthesized when unification gets stuck on it (Lean's synthPending). These are the
   order mixins the arithmetic tactics used to reach only through a hand-written table.
   Skipped when the Mathlib store is absent."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]))

(def ^:private mathlib-store
  (delay ((requiring-resolve 'ansatz.store/resolve-existing) "mathlib")))

(defn- with-mathlib [f]
  (if-let [path @mathlib-store]
    (let [saved-env @a/ansatz-env saved-idx @a/ansatz-instance-index]
      (try (binding [a/*verbose* false]
             (binding [*out* (java.io.StringWriter.)] (a/init! (str path) "mathlib"))
             (f))
           (finally (reset! a/ansatz-env saved-env)
                    (reset! a/ansatz-instance-index saved-idx))))
    (println "  (skipping instance-mathlib-test — no mathlib store)")))

(use-fixtures :once with-mathlib)

(defn- c [s ls] (e/const' (name/from-string s) ls))

(defn- class-goal
  "`C ℝ` as Lean elaborates it: the carrier, then each instance argument synthesized."
  [st env cls]
  (let [ci (env/lookup env (name/from-string cls))
        lps (vec (.levelParams ci))
        zs (vec (repeat (count lps) lvl/zero))]
    (loop [t (e/instantiate-level-params (.type ci) (zipmap lps zs)) acc [] first? true]
      (if (e/forall? t)
        (let [v (if first?
                  (c "Real" [])
                  (inst/synthesize* st env (inst/index-for env) (e/forall-type t) 0))]
          (recur (e/instantiate1 (e/forall-body t) v) (conj acc v) false))
        (apply e/app* (c cls zs) acc)))))

(def ^:private order-mixins
  ["ExistsAddOfLE" "PosMulMono" "MulPosMono" "PosMulStrictMono" "MulPosStrictMono"
   "AddLeftMono" "AddRightMono" "AddLeftReflectLE" "AddLeftReflectLT" "AddLeftStrictMono"
   "IsOrderedAddMonoid" "IsOrderedCancelAddMonoid" "IsOrderedRing" "ZeroLEOneClass"
   "HasDistribNeg"])

(deftest real-order-mixins-synthesize
  (let [env @a/ansatz-env]
    (doseq [cls order-mixins]
      (testing cls
        (let [st (tc/mk-tc-state env)
              goal (class-goal st env cls)
              r (inst/synthesize* st env (inst/index-for env) goal 0)]
          (is (some? r) (str cls " ℝ"))
          (when r
            (is (tc/is-def-eq st (tc/infer-type st r) goal) (str cls " ℝ: the answer has the goal's type"))))))))

(deftest implicit-class-binder-through-projections
  (testing "IsStrictOrderedRing.toPosMulStrictMono's {Semiring ℝ} is found by synthPending, as in Lean"
    (let [env @a/ansatz-env
          st (tc/mk-tc-state env)
          goal (e/app* (c "PosMulStrictMono" [lvl/zero]) (c "Real" [])
                       (c "Real.instMul" []) (c "Real.instZero" []) (c "Real.instPreorder" []))
          r (inst/synthesize* st env (inst/index-for env) goal 0)]
      (is (= "IsStrictOrderedRing.toPosMulStrictMono" (some-> r e/get-app-fn e/const-name name/->string)))
      (is (= "Real.semiring" (some-> r e/get-app-args second e/const-name name/->string))))))
