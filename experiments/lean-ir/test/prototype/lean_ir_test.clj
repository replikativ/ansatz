(ns prototype.lean-ir-test
  (:require [clojure.test :refer [deftest is testing run-tests]]
            [prototype.machine :as m]
            [prototype.examples :as examples]
            [prototype.import-ir :as ir]))

(deftest constant-space-mutual-tail-calls
  (let [s (examples/tail-demo 100000)]
    (is (= :done (:status s)))
    (is (= 0 (:result s)))
    (is (= 0 (get-in s [:stats :max-frames])))))

(deftest imported-list-map-preserves-sharing
  (let [unique (examples/list-demo false) shared (examples/list-demo true)]
    (is (= [2 3 4 5] (:values unique) (:values shared)))
    (is (= (:input unique) (:output unique)))
    (is (not= (:input shared) (:output shared)))
    (is (= [1 2 3 4] (:original shared)))
    (is (= 4 (get-in unique [:state :stats :allocations])))
    (is (= 8 (get-in shared [:state :stats :allocations])))
    (is (= 8 (get-in unique [:state :stats :field-stores])))
    ;; Both results can be dropped without dangling references or leaked guest nodes.
    (is (empty? (:heap (m/release (:state unique) (:output unique) 1))))
    (is (empty? (:heap (-> (:state shared)
                           (m/release (:input shared) 1)
                           (m/release (:output shared) 1)))))))

(deftest multi-shot-snapshot-with-logical-resource-drops
  (let [{:keys [captured left right]} (examples/fork-demo)]
    (is (= [10 20] [(:result left) (:result right)]))
    (is (= :suspended (:status captured)))
    (is (= 1 (count (:heap captured))))
    (is (empty? (:events captured)))
    (is (= [[:released :test-resource]] (:events left) (:events right)))
    (is (empty? (:heap left)))
    (is (empty? (:heap right)))
    (is (= 30 (:result (m/run (m/resume captured 30)))))))

(deftest snapshot-isolation-across-unique-field-stores
  (let [{:keys [initial target input]} (examples/list-demo false)
        captured (m/run (m/start initial target [(m/->Builtin :inc) input]) 20)
        left (m/run (m/resume captured nil))
        right (m/run (m/resume captured nil))]
    (is (= :paused (:status captured)))
    (is (pos? (count (:frames captured))))
    (is (= [1 2 3 4] (m/list-values captured input)))
    (is (= [2 3 4 5] (m/list-values left (:result left)) (m/list-values right (:result right))))
    (is (= input (:result left) (:result right)))))

(deftest fuel-pause-and-resume
  (let [s (m/start (m/world {:even (examples/tail-function :odd)
                             :odd (examples/tail-function :even)}) :even [100])
        paused (m/run s 7)]
    (is (= :paused (:status paused)))
    (is (= 0 (:result (m/run (m/resume paused nil)))))))

(deftest closure-ownership-transfers-and-shared-captures
  (let [fns {:use {:params [0 1] :body [:dec [:var 0] 1 [:return [:var 1]]]}
             :apply {:params [0] :body [:tail [:closure [:var 0]] [[:imm 42]]]}}
        [s resource] (m/resource (m/world fns) :captured)
        [s closure] (m/expr s [:closure :use [[:imm resource]]])
        unique (m/run (m/start s :apply [closure]))
        shared (m/run (m/start (m/retain s closure 1) :apply [closure]))]
    (is (= 42 (:result unique) (:result shared)))
    (is (= [[:released :captured]] (:events unique)))
    (is (empty? (:heap unique)))
    (is (empty? (:events shared)))
    (is (= [[:released :captured]] (:events (m/release shared closure 1))))))

(deftest invalid-ownership-and-unsupported-ir-fail-explicitly
  (let [[s root] (m/guest-list (m/world {}) [1])
        s (m/retain s root 1)
        s (assoc s :status :running :locals {0 root} :body [:set [:var 0] 0 [:imm 9] [:return [:var 0]]])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unique" (m/step s)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"underflow" (m/release s root 3))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported" (ir/expression {:reset {}}))))

(deftest arithmetic-and-budget-boundaries
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"step budget" (m/run (m/world {}) -1)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small integer"
                       (m/expr (m/world {}) [:prim :inc [[:imm 9007199254740991]]]))))

(defn -main [& _]
  (let [result (run-tests 'prototype.lean-ir-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
