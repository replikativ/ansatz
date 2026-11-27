(ns ansatz.indpred-below-test
  "Lean Meta/IndPredBelow.lean: `below` as an inductive predicate and `brecOn` as a theorem for
   recursive inductive predicates. Lean parity: test/lean-parity/dsl/indpred_below.lean."
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
  (binding [a/*verbose* false]
    (ind/define-inductive (a/env) "IpStep" []
      [['base [] [0]] ['next ['^:implicit n 'Nat 'h '(IpStep n)] '[(Nat.succ n)]]]
      :indices '[k Nat] :in 'Prop)
    (f)))

(use-fixtures :once fixtures/isolated-session with-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- infos [t] (loop [t t acc []] (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-info t))) acc)))

(deftest below-is-an-inductive-predicate
  (let [below (ci "IpStep.below")]
    (is (.isInduct below))
    (is (= 1 (.numParams below)) "the motive is its parameter")
    (is (= ["IpStep.below.base" "IpStep.below.next"] (mapv str (.ctors below))))
    (testing "next carries the field, its below proof, then its motive proof"
      (let [t (.type (ci "IpStep.below.next"))
            body (loop [t t k 0] (if (< k 2) (recur (e/forall-body t) (inc k)) t))
            [_ h] [(e/forall-type body) (e/forall-type (e/forall-body body))]]
        (is (= 5 (count (infos t))))
        (is (= "IpStep.below" (str (e/const-name (e/get-app-fn (e/forall-type (e/forall-body body)))))))))))

(deftest brec-on-is-a-checked-theorem
  (let [b (ci "IpStep.brecOn")]
    (is (.isThm b))
    (is (env/verifies? (a/env) (.type b) (.value b)))
    (is (= [:implicit :implicit :default :default] (infos (.type b))))
    (is (nil? (ci "IpStep.binductionOn")))))
