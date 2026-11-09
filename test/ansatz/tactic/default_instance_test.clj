(ns ansatz.tactic.default-instance-test
  "Lean default instances; Lean reference: test/lean/default_instances.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.tactic.default-instance :as di]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(defn- proves [params goal tactics]
  (a/prove-theorem (gensym "default_instance_") params goal tactics)
  true)

(deftest seed-is-leans-init-table
  (let [src (slurp "test/lean/default_instances.lean")
        block (second (re-find #"(?s)info: (.*?)\n-/" src))
        rows (set (map #(let [[c i p] (str/split % #" ")] [c i (parse-long p)])
                       (str/split-lines block)))]
    (is (= rows (set (for [[c entries] di/init-default-instances [i p] entries] [c i p]))))))

(deftest default-instances-resolve-heterogeneous-operators
  (testing "HDiv Int ?β ?γ takes instHDiv before 2 falls back to Nat"
    (is (proves '[a :- Int, x :- Int, h :- (= Int x (HDiv.hDiv a 2))] '(= Int x (HDiv.hDiv a 2))
                '[(exact h)]))
    (is (proves '[a :- Int, x :- Int, h :- (= Int (* 2 x) a)] '(= Int x (HDiv.hDiv a 2)) '[(omega)])))
  (testing "all-numeral operands still default to Nat"
    (is (proves '[] '(= Nat (HAdd.hAdd 2 3) 5) '[(rfl)])))
  (testing "apply leaves the numeral to the goal"
    (is (proves '[] '(Exists (fn [n :- Int] (= Int n n))) '[(apply (Exists.intro 0)) (rfl)]))
    (is (proves '[] '(Exists (fn [n :- Nat] (= Nat n n))) '[(apply (Exists.intro 0)) (rfl)]))))
