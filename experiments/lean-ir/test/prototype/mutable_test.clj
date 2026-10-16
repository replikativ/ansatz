(ns prototype.mutable-test
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.mutable :as u]
            [prototype.machine :as m]
            [prototype.examples :as ex]))

(defn compare-steps [initial]
  (let [mutable (u/thaw initial)]
    (loop [reference initial]
      (is (= reference (u/freeze mutable)))
      (when (= :running (:status reference))
        (u/step! mutable)
        (recur (m/step reference))))))

(deftest imported-map-lockstep
  (doseq [shared? [false true]]
    (let [{:keys [initial target input]} (ex/list-demo shared?)]
      (compare-steps (m/start initial target [(m/->Builtin :inc) input])))))

(deftest tail-loop-lockstep
  (compare-steps (m/start (m/world {:even (ex/tail-function :odd)
                                   :odd (ex/tail-function :even)}) :even [30])))

(deftest fork-live-frame-isolation
  (let [{:keys [initial target input]} (ex/list-demo false)
        initial (m/start initial target [(m/->Builtin :inc) input])
        machine (u/run! (u/thaw initial) 20)
        snapshot (u/freeze machine)
        left (u/thaw snapshot) right (u/thaw snapshot)]
    (is (= (m/run initial 20) snapshot))
    (is (seq (:frames snapshot)))
    (u/run! (u/resume! left nil))
    (is (= snapshot (u/freeze right) (u/freeze machine)))
    (u/run! (u/resume! right nil))
    (is (= (m/run (m/resume snapshot nil)) (u/freeze left) (u/freeze right)))
    (is (= [1 2 3 4] (m/list-values snapshot input)))))

(deftest snapshot-survives-mutable-parent-continuation
  (let [{:keys [initial target input]} (ex/list-demo false)
        machine (u/run! (u/thaw (m/start initial target [(m/->Builtin :inc) input])) 20)
        captured (u/freeze machine)]
    (u/run! (u/resume! machine nil))
    (is (= [1 2 3 4] (m/list-values captured input)))
    (is (= 20 (get-in captured [:stats :steps])))
    (is (= (m/run (m/resume captured nil)) (u/freeze machine)))))

(deftest suspended-resources-and-closures
  (let [snapshot (:captured (ex/fork-demo))]
    (doseq [value [10 20]]
      (is (= (m/run (m/resume snapshot value))
             (u/freeze (u/run! (u/resume! (u/thaw snapshot) value)))))))
  (let [fns {:use {:params [0 1] :body [:dec [:var 0] 1 [:return [:var 1]]]}
             :apply {:params [0] :body [:tail [:closure [:var 0]] [[:imm 42]]]}}
        [s resource] (m/resource (m/world fns) :capture)
        [s closure] (m/expr s [:closure :use [[:imm resource]]])]
    (doseq [s [s (m/retain s closure 1)]]
      (compare-steps (m/start s :apply [closure])))))

(defn -main [& _]
  (let [result (run-tests 'prototype.mutable-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
