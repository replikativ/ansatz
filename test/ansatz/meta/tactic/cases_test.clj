(ns ansatz.meta.tactic.cases-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.tactic.cases :as c]))

(def environment (delay (binding [a/*verbose* false] (a/load-init!))))

(deftest cases-on-nat-returns-constructor-fields-and-substitutions
  (let [ctx (c/context @environment)
        nat (u/const' "Nat" []) x (u/local-decl ctx "x" nat)
        goal (c/fresh-mvar! ctx nat)
        subgoals (c/cases ctx goal (e/fvar-id x))]
    (is (= ["Nat.zero" "Nat.succ"] (mapv (comp str :ctor-name) subgoals)))
    (is (= [0 1] (mapv (comp count :fields) subgoals)))
    (doseq [{:keys [mvar-id ctor-name fields subst]} subgoals]
      (c/with-goal! ctx mvar-id)
      (is (= (u/app (e/const' ctor-name []) fields) (get subst (e/fvar-id x))))
      (c/assign! ctx mvar-id (if (seq fields) (first fields) (e/lit-nat 42))))
    (c/with-goal! ctx goal)
    (let [value (u/mk-lambda-fvars ctx [x] (c/zonk ctx (e/mvar goal)))
          ci (env/mk-def (name/from-string "CasesReference.predecessor") []
                         (e/forall' "x" nat nat :default) value)
          out (env/check-constant @environment ci)]
      (is (some? (env/lookup out (.name ci)))))))

(deftest cases-refines-a-free-index-through-its-substitution
  (let [ctx (c/context @environment)
        nat (u/const' "Nat" []) n (u/local-decl ctx "n" nat)
        eq (u/local-decl ctx "h" (u/mk-eq ctx n (e/lit-nat 0)))
        goal (c/fresh-mvar! ctx nat)
        branches (c/cases ctx goal (e/fvar-id eq))]
    (is (= 1 (count branches)))
    (let [{:keys [mvar-id subst]} (first branches)]
      (is (some? (get subst (e/fvar-id n))))
      (c/with-goal! ctx mvar-id)
      (c/assign! ctx mvar-id (get subst (e/fvar-id n)))
      (c/with-goal! ctx goal)
      (let [value (u/mk-lambda-fvars ctx [n eq] (c/zonk ctx (e/mvar goal)))
            type (u/mk-forall-fvars ctx [n eq] nat)]
        (is (some? (env/check-constant @environment
                                       (env/mk-def (name/from-string "CasesReference.index") [] type value))))))))
