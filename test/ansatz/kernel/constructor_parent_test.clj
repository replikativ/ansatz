(ns ansatz.kernel.constructor-parent-test
  "A constructor must return its own type, even inside a mutual block whose other types it may
   mention: Lean's check_constructors, `is_valid_ind_app(t, idx)` for the constructor's own index.
   Native oracle: ConstructorParentOracle.lean."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env Expr Level Name]))

(defn- decl
  "mutual ParentA ParentB : Type with ParentA.mk : <a-result>, ParentB.mk : <b-result>."
  [unsafe? a-result b-result]
  (let [type (Expr/sort (Level/succ Level/ZERO_LEVEL) false)
        c #(Expr/mkConst (Name/fromString %) (object-array []) false)]
    (env/mk-inductive-decl [] 0 unsafe?
                           [["ParentA" type [["ParentA.mk" (c a-result)]]]
                            ["ParentB" type [["ParentB.mk" (c b-result)]]]])))

(deftest constructor-must-return-its-own-mutual-parent
  (doseq [unsafe? [false true]]
    (testing (str "parent check applies with unsafe=" unsafe?)
      (is (some? (env/add-inductive (Env.) (decl unsafe? "ParentA" "ParentB") 1000000)))
      (is (thrown-with-msg? RuntimeException #"invalid return type for 'ParentA.mk'"
                            (env/add-inductive (Env.) (decl unsafe? "ParentB" "ParentB") 1000000)))
      (is (thrown-with-msg? RuntimeException #"invalid return type for 'ParentB.mk'"
                            (env/add-inductive (Env.) (decl unsafe? "ParentA" "ParentA") 1000000))))))
