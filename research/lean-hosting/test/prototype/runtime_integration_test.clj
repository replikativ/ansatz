(ns prototype.runtime-integration-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.initialization :as init]
            [prototype.global-test :as globals]
            [prototype.interop :as interop]))

(defn linked []
  (let [catalogue (ir/index-bundles ["fixtures/runtime.jsonl"])
        named (fn [label] (first (filter #(= label (ir/name-label %)) (keys (:declarations catalogue)))))
        roots (mapv named ["RuntimeProbe.arraySize" "RuntimeProbe.arrayList" "RuntimeProbe.bump" "RuntimeProbe.taskMap"])]
    (assoc (init/link-local-plan catalogue roots abi/lower) :roots roots :catalogue catalogue :counter (named "RuntimeProbe.counter") :mode (named "RuntimeProbe.wasInitializing"))))

(deftest raw-primitives-from-native-export-work-in-all-backends
  (let [{:keys [functions roots counter mode] :as linked} (linked)
        [size list bump] roots
        parent (init/run-local-plan linked (m/world functions) :reference 1000)
        counter-ref (get-in parent [:globals counter :value])]
    (is (= 0 (:rc (m/node parent counter-ref))))
    (doseq [target [size list] run (globals/runners functions)]
      (let [initial (m/start parent target [10]) expected (m/run initial)]
        (is (= (if (= target size) 2 [10 11])
               (if (= target size) (:result expected) (m/list-values expected (:result expected)))))
        (doseq [fuel (range (inc (get-in expected [:stats :steps])))]
          (let [paused (run initial fuel)]
            (is (= (m/run initial fuel) paused))
            (when (= :paused (:status paused))
              (is (= expected (run (m/resume paused nil) 1000))))))))
    (doseq [run (globals/runners functions)]
      (let [initial (m/start parent bump [m/erased])
            left (run initial 1000) right (run initial 1000)
            second-left (run (m/start left bump [m/erased]) 1000)
            result-nat (fn [s] (first (:fields (m/node s (:result s)))))]
        (doseq [fuel (range 35)]
          (let [paused (run initial fuel)]
            (is (= (m/run initial fuel) paused))
            (when (= :paused (:status paused))
              (is (= left (run (m/resume paused nil) 1000))))))
        (is (= 41 (result-nat left) (result-nat right)))
        (is (= 42 (result-nat second-left)))
        (is (= (:heap left) (:heap right)))
        (is (= [40] (:fields (m/node parent counter-ref))))))))

(deftest native-array-function-through-public-interop
  (let [{:keys [catalogue roots]} (linked)]
    (doseq [backend [:reference :mutable :jvm]]
      (let [session (interop/open-session catalogue [(first roots)] {} backend)]
        (is (= 2 (:value (interop/call session "RuntimeProbe.arraySize" [10]))))))))

(deftest runtime-extern-admission-checks-types-ownership-and-backend
  (let [catalogue (:catalogue (linked))
        row (first (filter #(= "Nat.add" (ir/name-label (:name %))) (vals (:declarations catalogue))))
        ext (get-in row [:ir :extern])]
    (is (vector? (abi/lower row)))
    (doseq [changed [(assoc-in row [:ir :extern :type] "uint64")
                     (assoc-in row [:ir :extern :xs 0 :borrow] false)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type signature" (abi/lower changed))))
    (let [llvm {:standard {:backend ["str" ["anonymous"] "llvm"] :fn "wrong_backend"}}
          combined (update-in row [:ir :extern :ext :entries] #(into [llvm] %))]
      (is (= "lean_nat_add" (abi/symbol-for (get-in combined [:ir :extern]))))
      (is (= "lean_nat_add" (:runtime-extern (second (abi/lower combined))))))))

(deftest task-map-callback-is-an-explicit-resumable-guest-call
  (let [{:keys [functions roots] :as linked} (linked)
        parent (init/run-local-plan linked (m/world functions) :reference 1000)
        target (last roots) initial (m/start parent target [10]) expected (m/run initial)
        steps (- (get-in expected [:stats :steps]) (get-in initial [:stats :steps]))]
    (is (= 20 (:result expected)))
    (is (= (:heap parent) (:heap expected)))
    (doseq [run (globals/runners functions) fuel (range (+ 2 steps))]
      (let [paused (run initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= expected (run (m/resume paused nil) 1000))))))))
