(ns ansatz.tactic.instance-registry-test
  "The zero-config Init tier synthesizes against Lean's @[instance] registry (the bundled
   resources/ansatz/init-instances.tsv.gz), not against name-guessing: a class whose instances
   follow no naming convention resolves, and the elaborator sees the same index."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(deftest bundled-registry-is-installed
  (let [idx (a/instance-index)]
    (is (< 50 (count idx)) "hundreds of Init classes, not the 39 hand-listed ones")
    (is (= ["instNonemptyOfMonad" "instNonemptyOfInhabited"]
           (mapv (comp str :name) (inst/get-instances idx (name/from-string "Nonempty"))))
        "in Lean's order — most recently declared first")))

(deftest registry-only-class-synthesizes
  (testing "`Nonempty Nat` has no `instNonemptyNat`; only the registry knows instNonemptyOfInhabited"
    (let [env (a/env)
          goal (e/app (e/const' (name/from-string "Nonempty") [(lvl/succ lvl/zero)])
                      (e/const' (name/from-string "Nat") []))
          r (inst/synthesize* (tc/mk-tc-state env) env (inst/index-for env) goal 0)]
      (is (some? r))
      (is (= "instNonemptyOfInhabited" (str (e/const-name (e/get-app-fn r))))))))

(deftest re-registration-takes-the-later-priority
  (testing "`attribute [instance 50] C.toX` after the structure-parent registration at 1000 is one
            entry at priority 50 (Lean's DiscrTree.insertVal replaces the equal value in place)"
    (let [idx (inst/parse-instance-tsv ["ExistsAddOfLE\tCanonicallyOrderedAdd.toExistsAddOfLE\t1000"
                                        "ExistsAddOfLE\tAddGroup.existsAddOfLE\t100"
                                        "ExistsAddOfLE\tCanonicallyOrderedAdd.toExistsAddOfLE\t50"])]
      (is (= [["AddGroup.existsAddOfLE" 100] ["CanonicallyOrderedAdd.toExistsAddOfLE" 50]]
             (mapv (juxt (comp str :name) :priority)
                   (inst/get-instances idx (name/from-string "ExistsAddOfLE"))))))))
