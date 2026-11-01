(ns prototype.runtime-thunk-test
  (:require [prototype.machine :as m]
            [prototype.runtime-thunk :as thunk]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [prototype.raw-interop :as raw])
            #?(:clj [prototype.runtime-abi :as abi])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def backends #?(:clj [:reference :mutable :jvm] :cljs [:reference]))
(def compute ["str" ["anonymous"] "thunk-compute"])
(def getter ["str" ["anonymous"] "thunk-get"])
(defn functions [function]
  {compute function getter {:params [1 2] :body (thunk/get-own-body 2 3)}})
(defn run [backend world fuel]
  #?(:clj (case backend
            :reference (m/run world fuel)
            :mutable (u/freeze (u/run! (u/thaw world) fuel))
            :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world) fuel)))
     :cljs (m/run world fuel)))
(defn force-thunk [backend world value]
  (run backend (m/start world getter [m/erased value]) 10000))
(defn construct [world symbol value]
  (m/expr world [:runtime symbol [[:imm m/erased] [:imm value]]]))
(defn pending [function capture]
  (let [world (m/world (functions function))
        [world captured] (m/allocate world :ctor 9 [capture])
        [world closure] (m/expr world [:closure compute [[:imm captured]]])
        [world value] (construct world "lean_mk_thunk" closure)]
    {:world world :value value :closure closure :captured captured}))

(deftest construction-is-lazy-and-forcing-is-memoized-with-owned-results
  (doseq [backend backends]
    (let [{:keys [world value closure captured]} (pending {:params [1 2] :body [:return [:var 1]]} 42)
          _ (is (= {:kind :thunk :tag 251 :rc 1 :fields [closure] :thunk-state :pending} (m/node world value)))
          first-force (force-thunk backend world value)
          second-force (force-thunk backend first-force value)]
      (is (= captured (:result first-force)))
      (is (= captured (:result second-force)))
      (is (= :ready (:thunk-state (m/node first-force value))))
      (is (= [captured] (:fields (m/node first-force value))))
      (is (not (contains? (:heap first-force) (:id closure))))
      (is (= 2 (:rc (m/node first-force captured))))
      (is (= 3 (:rc (m/node second-force captured))))
      (is (= (:next-id world) (:next-id second-force)))
      (is (= :pending (:thunk-state (m/node world value))))
      (is (= 1 (:rc (m/node world captured))))
      (is (empty? (:heap (-> second-force (m/release captured 2) (m/release value 1))))))))

(deftest pure-thunks-transfer-values-and-borrow-the-thunk-when-read
  (doseq [backend backends]
    (let [world (m/world (functions {:params [1] :body [:unreachable]}))
          [world resource] (m/resource world "pure-thunk")
          [world value] (construct world "lean_thunk_pure" resource)
          after (force-thunk backend world value)]
      (is (= resource (:result after)))
      (is (= 1 (:rc (m/node after value))))
      (is (= 2 (:rc (m/node after resource))))
      (let [released (-> after (m/release value 1) (m/release resource 1))]
        (is (= [[:released "pure-thunk"]] (:events released)))
        (is (empty? (:heap released)))))))

(deftest every-fuel-pause-resumes-the-same-visible-force-without-host-recursion
  (doseq [backend backends fuel (range 0 8)]
    (let [{:keys [world value captured]} (pending {:params [1 2] :body [:return [:var 1]]} 7)
          paused (run backend (m/start world getter [m/erased value]) fuel)
          after (if (= :paused (:status paused)) (run backend (m/resume paused m/erased) 10000) paused)]
      (is (= :done (:status after)))
      (is (= captured (:result after)))
      (is (= :ready (:thunk-state (m/node after value))))
      (is (= 2 (:rc (m/node after captured)))))))

(deftest persistent-thunks-and-persistent-captures-can-be-forced-world-locally
  (doseq [backend backends]
    (let [{:keys [world value captured]} (pending {:params [1 2] :body [:return [:var 1]]} 12)
          persistent (m/mark-persistent world value)
          after (force-thunk backend persistent value)]
      (is (= 0 (:rc (m/node after value))))
      (is (= 0 (:rc (m/node after captured))))
      (is (= :ready (:thunk-state (m/node after value))))
      (is (= :pending (:thunk-state (m/node persistent value)))))))

(deftest failed-force-never-mutates-or-memoizes-the-parent-world
  (doseq [backend backends]
    (let [{:keys [world value closure]} (pending {:params [1 2] :body [:unreachable]} 7)]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"unreachable"
                           (force-thunk backend world value)))
      (is (= :pending (:thunk-state (m/node world value))))
      (is (= [closure] (:fields (m/node world value))))
      (is (= 1 (:rc (m/node world closure)))))))

(deftest recursive-force-is-an-explicit-single-threaded-runtime-limit
  (doseq [backend backends]
    (let [world (m/world (functions {:params [1 2] :body [:tail [:direct getter] [[:imm m/erased] [:var 1]]]}))
          [world closure] (m/expr world [:closure compute []])
          [world value] (construct world "lean_mk_thunk" closure)
          world (-> world (m/retain value 1) (assoc-in [:heap (:id closure) :fields] [value]))]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Recursive or concurrent"
                           (force-thunk backend world value)))
      (is (= :pending (:thunk-state (m/node world value)))))))

#?(:clj
   (deftest guest-host-callbacks-stay-visible-and-forks-memoize-independently
     (doseq [backend backends]
       (let [{:keys [world value]} (pending {:params [1 2]
                                            :body [:host "thunk-body" [[:var 1]] 3 [:return [:var 3]]]} 7)
             session (raw/open-functions (:functions world)
                       {"thunk-body" {:signature {:params [{:ty "object" :borrow false}] :return-type "object"}
                                      :handler (fn [_ state [argument]]
                                                 [(-> state (m/release argument 1)
                                                      (update-in [:environment :calls] (fnil inc 0)))
                                                  (get-in state [:environment :answer])])}}
                       {:backend backend})
             left (raw/call session (assoc world :environment {:answer 11}) getter [m/erased value])
             right (raw/call session (assoc world :environment {:answer 22}) getter [m/erased value])
             cached (raw/call session (:state left) getter [m/erased value])]
         (is (= 11 (:value left)))
         (is (= 22 (:value right)))
         (is (= 11 (:value cached)))
         (is (= 1 (get-in cached [:state :environment :calls])))
         (is (= [11] (:fields (m/node (:state left) value))))
         (is (= [22] (:fields (m/node (:state right) value))))
         (is (= :pending (:thunk-state (m/node world value))))))))

#?(:clj
   (deftest native-get-abi-lowers-only-after-borrow-type-validation
     (let [name ["str" ["anonymous"] "Thunk.get"]
           shape {:params [{:ty "erased" :borrow false} {:ty "object" :borrow true}] :return-type "object"}
           row {:name name :ir {:extern {:f name :xs [{:x {:idx 1} :ty "erased" :borrow false}
                                                       {:x {:idx 2} :ty "object" :borrow true}]
                                        :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn "lean_thunk_get_own"}}]}}}}]
       (with-redefs [abi/signatures (delay {"lean_thunk_get_own" [shape]})]
         (is (= (thunk/get-own-body 2 3) (get-in (abi/lower row) [1 :body])))
         (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type signature"
               (abi/lower (assoc-in row [:ir :extern :xs 1 :borrow] false))))))))
