(ns ansatz.structural-mutual-test
  "Structural recursion through multi-motive brecOn (mutual and nested types) and
   function-valued induction hypotheses (Lean Elab/PreDefinition/Structural/BRecOn.lean).
   Lean parity: test/lean-parity/dsl/structural_mutual.lean."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.fixtures :as fixtures]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- with-env [f]
  (reset! a/ansatz-env @test-env/bundled-init-env)
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.structural-mutual-test)]
    (ind/define-mutual-inductive (a/env) []
      [["SmTree" [['leaf []] ['node '[l SmTree f SmForest]]]]
       ["SmForest" [['nil []] ['cons '[t SmTree f SmForest]]]]])
    (f)))

(use-fixtures :once fixtures/isolated-session with-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- arity [n] (loop [t (.type (ci n)) k 0] (if (e/forall? t) (recur (e/forall-body t) (inc k)) k)))

(deftest a-mutual-block-is-one-declaration
  (testing "each type's recursor and brecOn take a motive (and a functional) per type"
    (is (= 2 (.numMotives (ci "SmTree.rec"))))
    (is (= ["SmTree" "SmForest"] (mapv str (.all (ci "SmForest")))))
    (doseq [n ["SmTree.below" "SmForest.below" "SmTree.brecOn" "SmForest.brecOn" "SmTree.casesOn"
               "SmForest.noConfusion"]]
      (is (some? (ci n)) n))
    ;; motive_1 motive_2 major F_1 F_2
    (is (= 5 (arity "SmTree.brecOn")))))

(deftest structural-recursion-on-one-type-of-a-group
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.structural-mutual-test)]
    (eval '(ansatz.core/defn sm-depth [t :- SmTree] Nat
             (match t (leaf) 0 (node l f) (+ (sm-depth l) 1))))
    (eval '(ansatz.core/theorem sm-depth-2 [] (= Nat (sm-depth (SmTree.node (SmTree.node SmTree.leaf SmForest.nil) SmForest.nil)) 2) (rfl))))
  (testing "Forest gets `fun _ => PUnit` and `fun _ _ => PUnit.unit`, as Lean"
    (is (re-find #"SmTree\.brecOn" (e/->string (.value (ci "sm-depth")))))
    (is (re-find #"PUnit\.unit" (e/->string (.value (ci "sm-depth"))))))
  (is (some? (ci "sm-depth-2"))))

(deftest nested-type-with-direct-recursion
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.structural-mutual-test)]
    (eval '(ansatz.core/inductive SmRose [] (leaf) (node [cs (List SmRose)] [r SmRose])))
    (eval '(ansatz.core/defn sm-rdepth [r :- SmRose] Nat
             (match r (leaf) 0 (node cs s) (+ (sm-rdepth s) 1))))
    (eval '(ansatz.core/theorem sm-rdepth-2 []
                                (= Nat (sm-rdepth (SmRose.node (List.nil SmRose) (SmRose.node (List.nil SmRose) SmRose.leaf))) 2) (rfl))))
  (is (re-find #"SmRose\.brecOn" (e/->string (.value (ci "sm-rdepth")))))
  (is (some? (ci "sm-rdepth-2"))))

(deftest function-valued-induction-hypothesis
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.structural-mutual-test)]
    (eval '(ansatz.core/inductive SmW [] (leaf) (branch [k (=> Nat SmW)])))
    (eval '(ansatz.core/defn sm-wleft [w :- SmW] Nat
             (match w (leaf) 0 (branch k) (+ (sm-wleft (k 0)) 1))))
    (eval '(ansatz.core/theorem sm-wleft-2 []
                                (= Nat (sm-wleft (SmW.branch (fn [_ :- Nat] (SmW.branch (fn [_ :- Nat] SmW.leaf))))) 2) (rfl))))
  (testing "the call `sm-wleft (k 0)` is answered from the dictionary `(a : Nat) → PProd …`"
    (is (re-find #"SmW\.brecOn" (e/->string (.value (ci "sm-wleft"))))))
  (is (some? (ci "sm-wleft-2"))))

(deftest doubly-nested-occurrences-come-from-the-kernel
  (testing "List (List Deep): one auxiliary below/brecOn per nested occurrence (Deep.below_1, _2)"
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.structural-mutual-test)]
      (eval '(ansatz.core/inductive SmDeep [] (node [cs (List (List SmDeep))]))))
    (is (= 2 (.numNested (ci "SmDeep"))))
    (doseq [n ["SmDeep.below_1" "SmDeep.below_2" "SmDeep.brecOn_2"]]
      (is (some? (ci n)) n))))
