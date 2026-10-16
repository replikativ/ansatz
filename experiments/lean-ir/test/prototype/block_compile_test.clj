(ns prototype.block-compile-test
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.block-compile :as b]
            [prototype.mutable :as u]
            [prototype.machine :as m]
            [prototype.heap-examples :as h]
            [prototype.examples :as ex]))

(defn map-start [shared?]
  (let [{:keys [initial target input]} (ex/list-demo shared?)]
    (m/start initial target [(m/->Builtin :inc) input])))

(defn compare-boundaries [program initial]
  (let [machine (u/thaw initial)]
    (loop [reference initial]
      (is (= reference (u/freeze machine)))
      (when (= :running (:status reference))
        (let [before (u/steps machine)]
          (b/step-block! program machine)
          (let [spent (- (u/steps machine) before)]
            (is (pos? spent))
            (recur (nth (iterate m/step reference) spent))))))))

(deftest imported-map-at-all-transfer-boundaries
  (let [initial (map-start false) program (b/compile-program (:functions initial))]
    (doseq [shared? [false true]] (compare-boundaries program (map-start shared?)))))

(deftest exact-fuel-pauses-and-cross-tier-resumption
  (let [initial (map-start false) program (b/compile-program (:functions initial))
        completed (m/run initial)]
    (doseq [fuel (range 81)]
      (let [machine (b/run! program (u/thaw initial) fuel)
            captured (u/freeze machine)]
        (is (= (m/run initial fuel) captured))
        (when (= :paused (:status captured))
          (is (= completed (u/freeze (b/run! program (u/resume! machine nil)))))
          (is (= completed (m/run (m/resume captured nil)))))))))

(deftest fork-with-live-compiled-return-frames
  (let [initial (map-start false) program (b/compile-program (:functions initial))
        machine (u/thaw initial)]
    (while (zero? (count (:frames (u/freeze machine)))) (b/step-block! program machine))
    (let [captured (u/freeze machine) left (u/thaw captured) right (u/thaw captured)]
      (is (seq (:frames captured)))
      (b/run! program left)
      (is (= captured (u/freeze right) (u/freeze machine)))
      (b/run! program right)
      (is (= (m/run captured) (u/freeze left) (u/freeze right)))
      (is (= [1 2 3 4] (m/list-values captured (get (:locals initial) 2)))))))

(deftest compiled-closures-and-synthetic-resource-drops
  (let [functions {:use {:params [0 1] :body [:dec [:var 0] 1 [:return [:var 1]]]}
                   :apply {:params [0] :body [:tail [:closure [:var 0]] [[:imm 42]]]}}
        [s resource] (m/resource (m/world functions) :capture)
        [s closure] (m/expr s [:closure :use [[:imm resource]]])
        program (b/compile-program functions)]
    (doseq [s [s (m/retain s closure 1)]]
      (compare-boundaries program (m/start s :apply [closure]))))
  (let [captured (:captured (ex/fork-demo)) program (b/compile-program (:functions captured))]
    (doseq [value [10 20]]
      (is (= (m/run (m/resume captured value))
             (u/freeze (b/run! program (u/resume! (u/thaw captured) value))))))))

(deftest program-and-coverage-guards
  (let [initial (map-start false) program (b/compile-program (:functions initial))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match"
                         (b/run! program (u/thaw (assoc initial :functions {})))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"step budget"
                         (b/run! program (u/thaw initial) -1))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                       (b/compile-program {:f {:params [] :body [:let 0 [:reset] [:return [:var 0]]]}}))))

(deftest imported-fold-reverse-and-guest-callback
  (let [functions (h/functions) program (b/compile-program functions)]
    (doseq [workload [:map :fold :reverse] xs [[] [0] [1 2 3 4]] shared? [false true]]
      (let [{:keys [initial input]} (h/prepare functions workload xs shared? true)
            expected (m/run initial)
            result (u/freeze (b/run! program (u/thaw initial)))
            released (cond-> (m/release result (:result result) 1) shared? (m/release input 1))]
        (is (= expected result (u/freeze (u/run! (u/thaw initial)))))
        (is (= (case workload :map (mapv inc xs) :fold (reduce + 0 xs) :reverse (vec (reverse xs)))
               (h/result-value result workload)))
        (is (empty? (:heap released)))))))

(deftest branching-tree-reuse-and-forks
  (let [functions (h/functions) program (b/compile-program functions)]
    (doseq [depth [0 1 3] shared? [false true]]
      (let [{:keys [initial input]} (h/prepare-tree functions depth shared?)
            parent (u/thaw initial) captured (u/freeze parent)
            result (u/freeze (b/run! program parent))
            child (u/freeze (b/run! program (u/thaw captured)))
            released (cond-> (m/release result (:result result) 1) shared? (m/release input 1))]
        (is (= (m/run initial) result child))
        (is (= (vec (reverse (range (bit-shift-left 1 depth)))) (h/tree-values result (:result result))))
        (is (= (vec (range (bit-shift-left 1 depth))) (h/tree-values captured input)))
        (is (empty? (:heap released)))))))

(deftest exact-addition-profile
  (is (= 6 (m/scalar :add [2 4])))
  (is (= 0 (m/scalar :add [9007199254740991 -9007199254740991])))
  (is (thrown? clojure.lang.ExceptionInfo (m/scalar :add [9007199254740991 1])))
  (is (thrown? clojure.lang.ExceptionInfo (m/scalar :add [1]))))

(deftest edited-guest-code-reuses-blocks-and-preserves-old-program
  (let [functions (h/functions) old (b/compile-program functions)
        edited (assoc-in functions [::h/inc :body] [:let 1 [:prim :dec [[:var 0]]] [:return [:var 1]]])
        new (b/compile-program edited old)
        old-start (:initial (h/prepare functions :map [1 2 3 4] false true))
        new-start (:initial (h/prepare edited :map [1 2 3 4] false true))
        left (u/freeze (b/run! old (u/thaw old-start)))
        right (u/freeze (b/run! new (u/thaw new-start)))]
    (is (= 1 (:compiled-blocks new)))
    (is (= (dec (count (:blocks old))) (:reused-blocks new)))
    (is (= [2 3 4 5] (m/list-values left (:result left))))
    (is (= [0 1 2 3] (m/list-values right (:result right))))
    (is (= (m/run old-start) left))
    (is (= (m/run new-start) right))
    (is (thrown? clojure.lang.ExceptionInfo (b/run! old (u/thaw new-start))))))

(deftest cache-respects-runtime-linking-profile
  (let [functions (h/functions)
        normal (binding [*compiler-options* (assoc *compiler-options* :direct-linking false)]
                 (b/compile-program functions))
        direct (binding [*compiler-options* (assoc *compiler-options* :direct-linking true)]
                 (b/compile-program functions normal))
        initial (:initial (h/prepare functions :map [1 2 3 4] false true))]
    (is (= (count (:blocks normal)) (:compiled-blocks direct)))
    (is (zero? (:reused-blocks direct)))
    (is (= (m/run initial) (u/freeze (b/run! direct (u/thaw initial)))))))

(defn -main [& _]
  (let [result (run-tests 'prototype.block-compile-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
