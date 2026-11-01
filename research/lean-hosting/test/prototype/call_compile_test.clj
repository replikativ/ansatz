(ns prototype.call-compile-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.block-compile :as b]
            [prototype.block-compile-test :as baseline]
            [prototype.region-compile-test :as regions]
            [prototype.heap-examples :as h]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(def profiles
  [{:lexical-joins true :leaf-calls true}
   {:lexical-joins true :compact-registers true}
   {:lexical-joins true :leaf-calls true :compact-registers true}])

(defn check-fuels [initial options]
  (let [program (b/compile-program (:functions initial) nil options)
        completed (m/run initial)]
    (baseline/compare-boundaries program initial)
    (doseq [fuel (range (+ 2 (get-in completed [:stats :steps])))]
      (let [machine (b/run! program (u/thaw initial) fuel)
            captured (u/freeze machine)]
        (is (= (m/run initial fuel) captured))
        (when (= :paused (:status captured))
          (is (= completed (u/freeze (b/run! program (u/resume! machine nil)))))
          (is (= completed (m/run (m/resume captured nil)))))))
    completed))

(deftest callback-calls-at-all-budgets
  (let [functions (h/functions)]
    (doseq [options profiles shared? [false true] workload [:map :fold :reverse]
            guest? (if (= :map workload) [false true] [true])]
      (check-fuels (:initial (h/prepare functions workload [1 2 3 4] shared? guest?)) options))))

(deftest captured-scalar-and-reference-ownership
  (doseq [options profiles shared? [false true]]
    (let [functions {:add h/add-function
                     :entry {:params [0] :body [:call 1 [:closure [:var 0]] [[:imm 7]] [:return [:var 1]]]}}
          [s closure] (m/expr (m/world functions) [:closure :add [[:imm 3]]])
          s (if shared? (m/retain s closure 1) s)]
      (is (= 10 (:result (check-fuels (m/start s :entry [closure]) options))))))
  ;; A scalar-leaf candidate that receives a resource must miss without consuming
  ;; it. The normal closure path transfers and eventually releases ownership.
  ;; Pinned lean_alloc_closure asserts fixed < arity; lean_apply_n requires n > 0.
  (let [functions {:identity {:params [0 2] :body [:return [:var 0]]}
                   :entry {:params [0] :body [:call 1 [:closure [:var 0]] [[:imm 0]]
                                             [:dec [:var 1] 1 [:return [:imm 99]]]]}}
        [s resource] (m/resource (m/world functions) :capture)
        [s closure] (m/expr s [:closure :identity [[:imm resource]]])]
    (doseq [options profiles]
      (let [result (check-fuels (m/start s :entry [closure]) options)]
        (is (= [[:released :capture]] (:events result)))
        (is (empty? (:heap result)))))))

(deftest compact-frames-suspend-fork-and-grow-for-tail-transfers
  (let [functions {:entry {:params [0] :body [:call 1 [:direct :small] [[:var 0]] [:return [:var 1]]]}
                   :small {:params [0] :body [:tail [:direct :wide] [[:var 0]]]}
                   :wide {:params [1000] :body [:suspend 1001 [:return [:var 1000]]]}}
        initial (m/start (m/world functions) :entry [42])]
    (doseq [options profiles]
      (let [captured (check-fuels initial options) program (b/compile-program functions nil options)
            parent (u/thaw captured)]
        (is (seq (:frames captured)))
        (doseq [answer [10 20]]
          (is (= (m/run (m/resume captured answer))
                 (u/freeze (b/run! program (u/resume! (u/thaw captured) answer))))))
        (is (= captured (u/freeze parent)))))))

(deftest guarded-overflow-miss-has-no-effects
  (let [functions {:add h/add-function
                   :entry {:params [0] :body [:call 1 [:closure [:var 0]] [[:imm 1]] [:return [:var 1]]]}}
        [s closure] (m/expr (m/world functions) [:closure :add [[:imm 9007199254740991]]])
        initial (m/start s :entry [closure])
        program (b/compile-program functions nil (last profiles))
        machine (assoc (u/thaw initial) :leaf-plans (:leaf-plans program))]
    (is (nil? (u/try-leaf! machine [:closure closure] [1])))
    (is (nil? (u/try-leaf! machine [:closure (m/->Builtin :inc)] [9007199254740991])))
    (is (= initial (u/freeze machine)))
    (doseq [fuel [0 1]]
      (is (= (m/run initial fuel) (u/freeze (b/run! program (u/thaw initial) fuel)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small integer"
                         (b/run! program (u/thaw initial))))))

(deftest edited-leaf-is-visible-to-reused-callers
  (let [functions (h/functions) options (last profiles)
        old (b/compile-program functions nil options)
        edited (assoc-in functions [::h/inc :body] [:let 1 [:prim :dec [[:var 0]]] [:return [:var 1]]])
        new (b/compile-program edited old options)
        direct (binding [*compiler-options* (assoc *compiler-options* :direct-linking true)]
                 (b/compile-program functions old options))
        initial (:initial (h/prepare edited :map [1 2 3 4] false true))
        stale (assoc new :leaf-plans (:leaf-plans old))]
    (is (= 1 (:compiled-blocks new)))
    (is (= 20 (:reused-blocks new)))
    (is (identical? (get-in old [:leaf-plans ::h/add :invoke]) (get-in new [:leaf-plans ::h/add :invoke])))
    (is (not (identical? (get-in old [:leaf-plans ::h/add :invoke]) (get-in direct [:leaf-plans ::h/add :invoke]))))
    (doseq [program [new stale]]
      (is (= (m/run initial) (u/freeze (b/run! program (u/thaw initial))))))
    (is (= (m/run (:initial (h/prepare functions :map [1 2 3 4] false true)))
           (u/freeze (b/run! old (u/thaw (:initial (h/prepare functions :map [1 2 3 4] false true)))))))))

(deftest suspended-nonleaf-and-direct-linked-helpers
  (binding [*compiler-options* (assoc *compiler-options* :direct-linking true)]
    (doseq [functions [regions/nested regions/captured-call]]
      (let [args (if (= functions regions/nested) [3 4] [3])]
        (check-fuels (m/start (m/world functions) :entry args) (last profiles))))
    (let [functions (h/functions) program (b/compile-program functions nil (last profiles))]
      (doseq [[workload guest?] [[:map false] [:map true] [:fold true]]]
        (let [initial (:initial (h/prepare functions workload [1 2 3 4] false guest?))]
          (is (= (m/run initial) (u/freeze (b/run! program (u/thaw initial))))))))))

(deftest maximum-leaf-budget-and-longer-fallback
  (doseq [increments [7 8]]
    (let [leaf {:params [0]
                :body (reduce (fn [body i] [:let i [:prim :inc [[:var (dec i)]]] body])
                              [:return [:var increments]] (reverse (range 1 (inc increments))))}
          caller {:params [0]
                  :body (reduce (fn [body i] [:call i [:direct :leaf] [[:var (dec i)]] body])
                                [:return [:var 6]] (reverse (range 1 7)))}
          functions {:leaf leaf :entry caller}]
      (is (= (* 6 increments)
             (:result (check-fuels (m/start (m/world functions) :entry [0]) (last profiles))))))))
