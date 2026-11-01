(ns prototype.region-compile-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.block-compile :as b]
            [prototype.block-compile-test :as baseline]
            [prototype.heap-examples :as h]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.examples :as ex]))

(defn program
  ([functions] (program functions nil))
  ([functions previous] (b/compile-program functions previous {:lexical-joins true})))

(def nested
  {:entry
   {:params [0 1]
    :body [:let 2 [:literal 10]
           [:join 42 [0 1]
            [:let 3 [:prim :add [[:var 0] [:var 1]]]
             [:join 43 [4]
              [:let 13 [:prim :add [[:var 3] [:var 4]]]
               [:suspend 5 [:let 14 [:prim :add [[:var 13] [:var 5]]] [:return [:var 14]]]]]
              [:let 3 [:prim :inc [[:var 3]]] [:jump 43 [[:var 3]]]]]]
            [:let 0 [:literal 100] [:jump 42 [[:var 1] [:var 0]]]]]]}})

(def captured-call
  {:entry {:params [7]
           :body [:join 42 [9]
                  [:let 13 [:prim :add [[:var 7] [:var 9]]] [:return [:var 13]]]
                  [:let 7 [:literal 100]
                   [:call 21 [:direct :worker] [[:var 7]] [:jump 42 [[:var 21]]]]]]}
   :worker {:params [5] :body [:suspend 11 [:return [:var 11]]]}})

(def recursive
  {:entry {:params [0]
           :body [:join 42 [1]
                  [:let 2 [:prim :zero? [[:var 1]]]
                   [:case [:var 2]
                    [[1 [:return [:var 1]]]
                     [0 [:let 3 [:prim :dec [[:var 1]]] [:jump 42 [[:var 3]]]]]]]]
                  [:jump 42 [[:var 0]]]]}})

(defn check-fuels [initial]
  (let [code (program (:functions initial))
        completed (m/run initial)
        steps (get-in completed [:stats :steps])]
    (baseline/compare-boundaries code initial)
    (doseq [fuel (range (+ 2 steps))]
      (let [machine (b/run! code (u/thaw initial) fuel)
            captured (u/freeze machine)]
        (is (= (m/run initial fuel) captured))
        (when (= :paused (:status captured))
          (is (= completed (u/freeze (b/run! code (u/resume! machine nil)))))
          (is (= completed (m/run (m/resume captured nil)))))))
    completed))

(deftest real-ir-boundaries-and-exact-pauses
  (let [functions (h/functions)]
    (doseq [shared? [false true]]
      (doseq [workload [:map :fold :reverse]]
        (check-fuels (:initial (h/prepare functions workload [1 2 3 4] shared? true))))
      (check-fuels (:initial (h/prepare-tree functions 3 shared?))))))

(deftest lexical-captures-parallel-arguments-and-forked-suspension
  (doseq [[functions args expected] [[nested [3 4] 209] [captured-call [3] 3]]]
    (let [initial (m/start (m/world functions) :entry args)
          captured (check-fuels initial)
          code (program functions)
          parent (u/thaw captured)]
      (is (= :suspended (:status captured)))
      (doseq [answer [10 20]]
        (let [child (u/thaw captured)
              result (u/freeze (b/run! code (u/resume! child answer)))]
          (is (= (m/run (m/resume captured answer)) result))
          (is (= (+ expected answer) (:result result)))
          (is (= captured (u/freeze parent)))))
      (b/run! code (u/resume! parent 30))
      (is (= captured (u/freeze (u/thaw captured)))))))

(deftest recursive-and-shadowed-joins-fall-back-with-correct-state
  (is (= 0 (:result (check-fuels (m/start (m/world recursive) :entry [12])))))
  (let [functions {:entry {:params [0]
                           :body [:join 42 [1]
                                  [:join 42 [2] [:return [:var 2]] [:jump 42 [[:var 1]]]]
                                  [:jump 42 [[:var 0]]]]}}]
    (is (= 7 (:result (check-fuels (m/start (m/world functions) :entry [7]))))))
  (is (pos? (reduce + (map :inlined-jumps (vals (:blocks (program recursive))))))))

(deftest scalar-tail-callback-keeps-terminal-diagnostic-registers
  (let [functions {:entry {:params [0]
                           :body [:let 1 [:prim :inc [[:var 0]]]
                                  [:join 42 [2] [:tail [:closure [:imm (m/->Builtin :inc)]] [[:var 2]]]
                                   [:jump 42 [[:var 1]]]]]}}]
    (check-fuels (m/start (m/world functions) :entry [5]))))

(deftest synthetic-resource-ownership-through-regions
  (let [captured (:captured (ex/fork-demo)) code (program (:functions captured))]
    (doseq [answer [10 20]]
      (is (= (m/run (m/resume captured answer))
             (u/freeze (b/run! code (u/resume! (u/thaw captured) answer))))))))

(deftest cache-respects-region-mode-and-tail-signatures
  (let [functions (h/functions) old (b/compile-program functions) regions (program functions old)
        edited (assoc-in functions [::h/inc :body] [:let 1 [:prim :dec [[:var 0]]] [:return [:var 1]]])
        new (program edited regions)
        changed-arity (program (assoc-in edited [::h/inc :params] [0 1]) new)
        initial (:initial (h/prepare edited :map [1 2 3 4] false true))]
    (is (zero? (:reused-blocks regions)))
    (is (= 1 (:compiled-blocks new)))
    (is (= 20 (:reused-blocks new)))
    (is (zero? (:reused-blocks changed-arity)))
    (is (= (m/run initial) (u/freeze (b/run! new (u/thaw initial)))))))

(deftest direct-linked-region-helpers
  (binding [*compiler-options* (assoc *compiler-options* :direct-linking true)]
    (check-fuels (m/start (m/world nested) :entry [3 4]))
    (check-fuels (m/start (m/world captured-call) :entry [3]))))
