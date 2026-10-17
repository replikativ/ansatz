(ns prototype.runtime-profile-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.raw-interop :as raw]))

(def entry ["str" ["str" ["anonymous"] "Lean"] "profileit"])
(def compute ["str" ["anonymous"] "profile-compute"])
(defn functions [body]
  {entry {:params [1 2 3 4 5] :body (abi/profileit-body [1 2 3 4 5] 6)}
   ;; Stand-in tests only getter ABI/ownership. Production calls the actual
   ;; source-collected Options lookup, not this stand-in representation.
   abi/profiler-option-getter {:params [1] :body [:let 2 [:project [:var 1] 0]
                                                  [:dec [:var 1] 1 [:return [:var 2]]]]}
   compute {:params [1 2] :body body}})
(defn fixture [enabled body]
  (let [world (m/world (functions body))
        [world options] (m/allocate world :ctor 0 [enabled])
        [world declaration] (m/resource world "decl-owner")
        [world value] (m/resource world "result-owner")
        [world closure] (m/expr world [:closure compute [[:imm value]]])]
    {:world world :options options :declaration declaration :value value :closure closure
     :arguments [m/erased "parsing" options closure declaration]}))
(defn run [backend world fuel]
  (case backend :reference (m/run world fuel)
                :mutable (u/freeze (u/run! (u/thaw world) fuel))
                :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world) fuel))))

(deftest disabled-profileit-executes-owned-closure-and-preserves-borrowed-options
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world options declaration value closure arguments]}
          (fixture 0 [:return [:var 1]])
          after (run backend (m/start world entry arguments) 1000)]
      (is (= value (:result after)))
      (is (= 1 (:rc (m/node after options))))
      (is (= 1 (:rc (m/node after value))))
      (is (not (contains? (:heap after) (:id declaration))))
      (is (not (contains? (:heap after) (:id closure))))
      (is (= [[:released "decl-owner"]] (:events after)))
      (is (= [[:released "decl-owner"] [:released "result-owner"]]
             (:events (m/release after value 1))))
      (is (= 1 (:rc (m/node world options)))))))

(deftest enabled-profileit-is-an-explicit-capability-limit-before-closure-execution
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world arguments]} (fixture 1 [:unreachable])
          error (try (run backend (m/start world entry arguments) 1000) nil
                     (catch clojure.lang.ExceptionInfo e e))]
      (is (= :enabled-profiling (get-in (ex-data error) [:declaration :runtime-limit])))
      (is (re-find #"clock/event" (get-in (ex-data error) [:declaration :message])))
      (is (empty? (:events world))))))

(deftest disabled-profileit-preserves-fuel-and-raw-host-call-visibility
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world arguments value]} (fixture 0 [:host "profile-body" [[:var 1]] 3 [:return [:var 3]]])
          session (raw/open-functions (:functions world)
                    {"profile-body" {:signature {:params [{:ty "object" :borrow false}] :return-type "object"}
                                     :handler (fn [_ w [x]] [w x])}} {:backend backend})]
      (doseq [fuel (range 7)]
        (let [paused (run backend (m/start world entry arguments) fuel)
              resumed (raw/continue session paused)]
          (is (= value (:value resumed)))
          (is (= 1 (:rc (m/node (:state resumed) value)))))))))

(deftest profileit-lowering-is-guarded-by-the-real-pinned-getter-and-exact-abi
  (let [shape {:params [{:ty "erased" :borrow false} {:ty "object" :borrow true}
                        {:ty "object" :borrow true} {:ty "tobject" :borrow false}
                        {:ty "tobject" :borrow false}] :return-type "tobject"}
        row {:name entry :ir {:extern {:f entry :xs (mapv #(assoc %1 :x {:idx %2}) (:params shape) (range 1 6))
                                       :type "tobject" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn "lean_profileit"}}]}}}}]
    (with-redefs [abi/signatures (delay {"lean_profileit" [shape]})]
      (is (= (abi/profileit-body [1 2 3 4 5] 6) (get-in (abi/lower row) [1 :body])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type signature"
            (abi/lower (assoc-in row [:ir :extern :xs 2 :borrow] false)))))))
