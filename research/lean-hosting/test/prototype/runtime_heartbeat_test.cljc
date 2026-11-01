(ns prototype.runtime-heartbeat-test
  (:require [prototype.machine :as m] [prototype.runtime-heartbeat :as heartbeat]
            [prototype.native-scalar :as native]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def get-op "lean_io_get_num_heartbeats")
(def set-op "lean_io_set_heartbeats")
(def ops {:get-task-runtime :task-runtime :set-task-runtime #(assoc %1 :task-runtime %2)
          :allocation-count m/heartbeat-allocation-count :node m/node :ref? m/ref? :release m/release})
(defn read-counter [world] (m/expr world [:runtime get-op [[:imm m/erased]]]))
(defn reset-counter [world value] (m/expr world [:runtime set-op [[:imm value] [:imm m/erased]]]))
(defn allocate-n [world n] (nth (iterate #(first (m/allocate % :ctor 0 [])) world) n))

(deftest reads-resets-and-forks-use-guest-allocation-counts
  (let [world (allocate-n (m/world {}) 4)
        [world n] (read-counter world)
        _ (is (= 4 n))
        [world unit] (reset-counter world (native/native-scalar 100))
        a (allocate-n world 3) b (allocate-n world 1)]
    (is (= 0 unit))
    (is (= 103 (second (read-counter a))))
    (is (= 101 (second (read-counter b))))
    (is (= 100 (second (read-counter world))))
    ))

(deftest fixed-width-reset-profile
  #?(:clj (let [[world _] (reset-counter (m/world {}) 18446744073709551615N)]
            (is (= 0 (second (read-counter (allocate-n world 1))))))
     :cljs (is (thrown? js/Error (reset-counter (m/world {}) 9007199254740992)))))

(deftest logical-thread-switches-isolate-async-and-share-sync-costs
  (let [world (allocate-n (m/world {}) 2)
        world (heartbeat/switch-thread ops world :worker)
        world (allocate-n world 3)
        world (heartbeat/switch-thread ops world :main)
        world (allocate-n world 1)
        world (heartbeat/switch-thread ops world :main)
        counts (get-in world [:task-runtime :heartbeats :counts])]
    (is (= {:main 3 :worker 3} counts))
    (is (= 3 (second (read-counter world))))
    (is (= :main (get-in world [:task-runtime :heartbeats :thread])))))

(deftest lazy-id-reservations-do-not-charge-local-allocations
  (let [world (allocate-n (m/world {}) 2)
        [world _] (read-counter world)
        imported (-> world (update-in [:stats :allocations] + 10000)
                     (assoc :heartbeat-allocation-offset 10000))]
    (is (= 2 (second (read-counter imported))))
    (is (= 3 (second (read-counter (allocate-n imported 1)))))
    #?(:clj (is (= (select-keys imported [:stats :task-runtime :heartbeat-allocation-offset])
                     (select-keys (u/freeze (u/thaw imported)) [:stats :task-runtime :heartbeat-allocation-offset]))))))

(deftest owned-mpz-reset-releases-and-truncates-as-uint64
  (let [[world value] (m/allocate (m/world {}) :mpz 250 [])
        world (assoc-in world [:heap (:id value) :integer] #?(:clj 18446744073709551621N :cljs 12345))
        [world unit] (reset-counter world value)]
    (is (= 0 unit))
    (is (not (contains? (:heap world) (:id value))))
    (is (= #?(:clj 5 :cljs 12345) (second (read-counter world))))))

#?(:clj
   (deftest execution-tiers-observe-identical-heartbeats
     (let [functions {:run {:params []
                            :body [:let 0 [:runtime set-op [[:imm 7] [:imm m/erased]]]
                                   [:let 1 [:ctor 0 [[:imm 1]]]
                                    [:let 2 [:runtime get-op [[:imm m/erased]]]
                                     [:dec [:var 1] 1 [:return [:var 2]]]]]]}}
           initial (m/start (m/world functions) :run [])
           expected (m/run initial)]
       (is (= 8 (:result expected)))
       (doseq [run [u/run! #(lazy/run! (lazy/open-program functions) %)]]
         (is (= expected (u/freeze (run (u/thaw initial)))))))))

(defn- waiting-task [world sync?]
  (let [[world task] (m/allocate world :task 252 [])]
    [(assoc-in world [:heap (:id task)]
               (assoc (m/node world task) :task-state :waiting :sync? sync?)) task]))
(defn- task-op [world symbol args]
  (m/expr world [:runtime symbol (mapv #(vector :imm %) args)]))

(deftest scheduler-hooks-preserve-parent-and-synchronous-task-counters
  (let [[world outer] (waiting-task (m/world {}) false)
        [world sync] (waiting-task world true)
        [world async] (waiting-task world false)
        [world _] (reset-counter world 100)
        [world _] (task-op world "prototype_task_begin" [outer])
        world (allocate-n world 2)
        [world n] (read-counter world)
        [world _] (task-op world "prototype_task_begin" [sync])
        world (allocate-n world 3)
        [world sync-n] (read-counter world)
        [world _] (task-op world "prototype_task_publish" [sync 0])
        [world _] (task-op world "prototype_task_begin" [async])
        world (allocate-n world 4)
        [world async-n] (read-counter world)
        [world _] (task-op world "prototype_task_publish" [async 0])
        [world outer-n] (read-counter world)
        [world _] (task-op world "prototype_task_publish" [outer 0])]
    (is (= 2 n))
    (is (= 5 sync-n))
    (is (= 4 async-n))
    (is (= 5 outer-n))
    (is (= 100 (second (read-counter world))))
    (is (= [] (get-in world [:task-runtime :active])))
    (is (= outer (:thread-key (m/node world sync))))
    (is (= async (:thread-key (m/node world async))))))

#?(:cljs
   (deftest javascript-counter-overflow-fails-explicitly
     (let [[world _] (reset-counter (m/world {}) 9007199254740991)]
       (is (= 9007199254740991 (second (read-counter world))))
       (is (thrown? js/Error (read-counter (allocate-n world 1)))))))

(deftest invalid-or-rewound-allocation-providers-fail-closed
  (doseq [n [-1 1.5 #?(:clj nil :cljs 9007199254740992)]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (heartbeat/switch-thread (assoc ops :allocation-count (constantly n)) (m/world {}) :main))))
  (let [world (assoc (m/world {}) :task-runtime
                     {:queue [] :active [] :heartbeats {:thread :main :mark 3 :counts {:main 9}}})]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (heartbeat/switch-thread (assoc ops :allocation-count (constantly 2)) world :main)))
    (is (= 9 (get-in world [:task-runtime :heartbeats :counts :main])))))
