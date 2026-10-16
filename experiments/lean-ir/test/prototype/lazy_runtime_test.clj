(ns prototype.lazy-runtime-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.block-compile :as b]
            [prototype.import-ir :as ir]
            [prototype.lazy-runtime :as lazy]
            [prototype.heap-examples :as h]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.region-compile-test :as regions]))

(defn check-fuels [functions initial]
  (let [program (lazy/open-program functions) completed (m/run initial)]
    (is (zero? (:compiled (lazy/summary program))))
    (doseq [fuel (range (+ 2 (get-in completed [:stats :steps])))]
      (let [machine (lazy/run! program (u/thaw initial) fuel) captured (u/freeze machine)]
        (is (= (m/run initial fuel) captured))
        (when (= :paused (:status captured))
          (is (= completed (u/freeze (lazy/run! program (u/resume! machine nil)))))
          (is (= completed (m/run (m/resume captured nil)))))))
    completed))

(deftest real-ir-pauses-and-suspension-forks
  (let [functions (h/functions)]
    (doseq [shared? [false true] workload [:map :fold :reverse]]
      (check-fuels functions (:initial (h/prepare functions workload [1 2 3 4] shared? true)))))
  (doseq [functions [regions/nested regions/captured-call regions/recursive]]
    (let [initial (m/start (m/world functions) :entry (if (= functions regions/nested) [3 4] [3]))
          captured (check-fuels functions initial)]
      (when (= :suspended (:status captured))
        (let [program (lazy/open-program functions) parent (u/thaw captured)]
          (doseq [answer [10 20]]
            (is (= (m/run (m/resume captured answer))
                   (u/freeze (lazy/run! program (u/resume! (u/thaw captured) answer))))))
          (is (= captured (u/freeze parent))))))))

(deftest unvisited-declarations-are-not-compiled
  (let [functions {:entry {:params [] :body [:return [:imm 42]]}
                   :unused {:params [] :body [:unsupported]}}
        program (lazy/open-program functions)
        initial (m/start (m/world functions) :entry [])]
    (lazy/run! program (u/thaw initial) 0)
    (is (zero? (:compiled (lazy/summary program))))
    (is (= (m/run initial) (u/freeze (lazy/run! program (u/thaw initial)))))
    (is (= 1 (:compiled (lazy/summary program))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                         (lazy/run! program (u/thaw (m/start (m/world functions) :unused [])))))))

(deftest edits-reuse-caller-code-without-stale-callees
  (let [functions {:entry {:params [] :body [:tail [:direct :value] []]}
                   :value {:params [] :body [:return [:imm 10]]}}
        cache (lazy/code-cache)
        old (lazy/open-program functions {} cache)
        run #(u/freeze (lazy/run! % (u/thaw (m/start (m/world (:functions %)) :entry []))))
        before (run old)
        edited (assoc-in functions [:value :body] [:return [:imm 20]])
        new (lazy/open-program edited {} cache)
        after (run new)]
    (is (= 10 (:result before)))
    (is (= 20 (:result after)))
    (is (= 1 (:compiled (lazy/summary new))))
    (is (= 1 (:cache-hits (lazy/summary new))))
    (is (= before (run old)))
    ;; Only the tail target's shape affects this entry, not unrelated arities.
    (let [unrelated (lazy/open-program (assoc edited :unused {:params [0] :body [:unsupported]}) {} cache)]
      (is (= 20 (:result (run unrelated))))
      (is (zero? (:compiled (lazy/summary unrelated)))))
    (is (not= (b/runtime-block-key functions (get-in functions [:entry :body]) {:lexical-joins true})
              (b/runtime-block-key (assoc-in functions [:value :params] [0])
                                   (get-in functions [:entry :body]) {:lexical-joins true})))
    (is (not= (b/runtime-block-key functions [:return [:imm 0]] {})
              (b/runtime-block-key functions [:return [:imm 0]] {:direct-linking true})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match"
                         (lazy/run! old (u/thaw (m/start (m/world edited) :entry [])))))))

(deftest selective-real-ir-lowering
  (let [catalogue (ir/index-bundles ["fixtures/list-map.jsonl" "fixtures/list-fold.jsonl"])
        eager (ir/load-bundle "fixtures/list-map.jsonl")
        root (h/entry eager "List.map")
        selected (ir/load-closure catalogue [root])]
    (is (= eager selected))
    (let [target (h/entry eager "List.map._redArg")
          functions (ir/load-closure catalogue [target])
          [world input] (m/guest-list (m/world functions) [1 2 3 4])
          initial (m/start world target [(m/->Builtin :inc) input])
          result (u/freeze (lazy/run! (lazy/open-program functions) (u/thaw initial)))]
      (is (= (m/run initial) result))
      (is (= [2 3 4 5] (m/list-values result (:result result)))))
    (let [name ["str" ["anonymous"] "unsupported"]
          catalogue (assoc-in catalogue [:declarations name]
                              {:name name :kind "decl" :ir {:extern {}}})]
      (is (= selected (ir/load-closure catalogue [root])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing body or extern"
                           (ir/load-closure catalogue [name]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing declaration dependency"
                         (ir/load-closure (assoc catalogue :declarations {}) [root])))))

(deftest cache-reload-guard-and-profile-boundaries
  (let [functions {:entry {:params [] :body [:return [:imm 0]]}}
        program (lazy/open-program functions)
        initial (m/start (m/world functions) :entry [])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Reopen lazy program"
                         (lazy/run! (assoc program :generation (Object.)) (u/thaw initial))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Lazy prototype"
                         (lazy/open-program functions {:leaf-calls true})))))
