(ns prototype.runtime-task-test
  (:refer-clojure :exclude [promise])
  (:require [prototype.machine :as m]
            [prototype.runtime-task :as task]
            [prototype.native-scalar :as native]
            [prototype.runtime-prim :as prim]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [prototype.raw-interop :as raw])
            #?(:clj [prototype.runtime-abi :as abi])
            #?(:clj [prototype.import-ir :as ir])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def backends #?(:clj [:reference :mutable :jvm] :cljs [:reference]))
(def functions
  (assoc (into {} (for [[symbol {:keys [arity]}] (assoc task/supported-symbols "lean_task_pure" {:arity 2})
                       :let [params (vec (range 1 (inc arity))) dest (inc arity)]]
                   [symbol {:params params :body [:let dest [:runtime symbol (mapv #(vector :var %) params)]
                                                  [:return [:var dest]]]}]))
         "drop" {:params [1] :body [:dec [:var 1] 1 [:return [:imm 0]]]}))
(defn run-op [backend world symbol args]
  (let [world (m/start world symbol args)]
    #?(:clj (case backend :reference (m/run world)
                          :mutable (u/freeze (u/run! (u/thaw world)))
                          :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world))))
       :cljs (m/run world))))
(defn result-task [world promise]
  (m/expr world [:runtime "lean_io_promise_result_opt" [[:imm m/erased] [:imm promise]]]))
(defn promise [] (m/expr (m/world functions) [:runtime "lean_io_promise_new"
                                          [[:imm m/erased] [:imm m/erased] [:imm m/erased]]]))

(deftest new-promise-is-pending-with-one-shared-result-task
  (doseq [backend backends]
    (let [world (run-op backend (m/world functions) "lean_io_promise_new" [m/erased m/erased m/erased])
          promise (:result world) [world a] (result-task world promise) [world b] (result-task world promise)
          status (run-op backend world "lean_io_get_task_state" [m/erased a m/erased])]
      (is (= :promise (:kind (m/node world promise))))
      (is (= a b))
      (is (= 3 (:rc (m/node world a))))
      (is (= :promise-pending (:task-state (m/node world a))))
      (is (= 1 (:result status)))
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Unresolved guest task"
                           (run-op backend world "lean_task_get_own" [m/erased a]))))))

(deftest first-resolve-wins-and-duplicate-owned-values-are-released
  (doseq [backend backends]
    (let [[world promise] (promise) [world result-task] (result-task world promise)
          [world first] (m/resource world "first") [world second] (m/resource world "second")
          resolved (run-op backend world "lean_io_promise_resolve" [m/erased first promise m/erased])
          duplicate (run-op backend resolved "lean_io_promise_resolve" [m/erased second promise m/erased])
          status (run-op backend duplicate "lean_io_get_task_state" [m/erased result-task m/erased])
          read (run-op backend status "lean_task_get_own" [m/erased result-task])
          option (:result read)
          unwrapped (run-op backend read "lean_option_get_or_block" [m/erased m/erased option])]
      (is (= 2 (:result status)))
      (is (= [[:released "second"]] (:events duplicate)))
      (is (= first (:result unwrapped)))
      (is (= 2 (:rc (m/node unwrapped first))))
      (let [released (-> unwrapped (m/release promise 1) (m/release first 1))]
        (is (empty? (:heap released)))
        (is (= [[:released "second"] [:released "first"]] (:events released))))
      (is (= :promise-pending (:task-state (m/node world result-task)))))))

(deftest dropping-last-promise-owner-resolves-task-to-none
  (doseq [backend backends]
    (let [[world promise] (promise) [world result-task] (result-task world promise)
          retained (m/retain world promise 1)
          one-owner-left (run-op backend retained "drop" [promise])
          dropped (run-op backend one-owner-left "drop" [promise])
          read (run-op backend dropped "lean_task_get_own" [m/erased result-task])]
      (is (= :promise-pending (:task-state (m/node one-owner-left result-task))))
      (is (= :ready (:task-state (m/node dropped result-task))))
      (is (= 0 (:result read)))
      (is (empty? (:heap read)))
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Dropped promise"
                           (run-op backend read "lean_option_get_or_block" [m/erased m/erased 0]))))))

(deftest promise-resolution-and-cancellation-are-snapshot-local
  (doseq [backend backends]
    (let [[world promise] (promise) [world t] (result-task world promise)
          left (run-op backend world "lean_io_promise_resolve" [m/erased 11 promise m/erased])
          right (run-op backend world "lean_io_promise_resolve" [m/erased 22 promise m/erased])
          cancelled (run-op backend world "lean_io_cancel" [m/erased t m/erased])
          left-read (run-op backend left "lean_task_get_own" [m/erased t])
          right-read (run-op backend right "lean_task_get_own" [m/erased t])]
      (is (= [11] (:fields (m/node left-read (:result left-read)))))
      (is (= [22] (:fields (m/node right-read (:result right-read)))))
      (is (true? (:cancelled? (m/node cancelled t))))
      (is (= :promise-pending (:task-state (m/node cancelled t))))
      (is (nil? (:cancelled? (m/node world t))))
      (is (= :promise-pending (:task-state (m/node world t)))))))

(deftest historical-task-pure-get-contract-remains-compatible
  (doseq [backend backends]
    (let [world (run-op backend (m/world functions) "lean_task_pure" [m/erased 42])
          task (:result world) read (run-op backend world "lean_task_get_own" [m/erased task])]
      (is (= 42 (:result read)))
      (is (empty? (:heap read)))))
  (is (not-any? #(.startsWith % "prototype_") (keys task/supported-symbols))))

(def drain-target ["str" ["anonymous"] "drain-tasks"])
(defn scheduled-functions [extra]
  (merge
   (into {} (for [[symbol {:keys [arity]}] task/supported-symbols
                  :let [params (vec (range 1 (inc arity))) dest (inc arity)]]
              [symbol {:params params
                       :body (cond
                               (= symbol "lean_task_get_own") (task/get-body 2 dest)
                               (= symbol "lean_io_wait") [:tail [:direct task/get-target] [[:var 1] [:var 2]]]
                               (= symbol "lean_io_wait_any") (task/wait-any-body 2 dest)
                               (= symbol "lean_io_promise_resolve")
                               [:let dest [:runtime symbol (mapv #(vector :var %) params)] (task/drain-body (inc dest) true)]
                               (contains? #{"lean_task_spawn" "lean_task_map" "lean_task_bind" "lean_io_as_task" "lean_io_map_task" "lean_io_bind_task"} symbol)
                               (task/registration-body symbol params dest)
                               :else [:let dest [:runtime symbol (mapv #(vector :var %) params)] [:return [:var dest]]])}]))
   {task/get-target {:params [1 2] :body (task/get-body 2 3)}
    "lean_task_pure" {:params [1 2] :body [:let 3 [:runtime "lean_task_pure" [[:var 1] [:var 2]]] [:return [:var 3]]]}
    "drop" (get functions "drop")
    drain-target {:params [] :body (task/drain-body 1 false)}} extra))
(defn run-state [backend world fuel]
  #?(:clj (case backend :reference (m/run world fuel)
                        :mutable (u/freeze (u/run! (u/thaw world) fuel))
                        :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world) fuel)))
     :cljs (m/run world fuel)))
(defn scheduled-call [backend world target args]
  (run-state backend (m/start world target args) 100000))
(defn task-closure [world target captures]
  (m/expr world [:closure target (mapv #(vector :imm %) captures)]))
(defn new-promise [world]
  (m/expr world [:runtime "lean_io_promise_new" [[:imm m/erased] [:imm m/erased] [:imm m/erased]]]))

(deftest baseio-jobs-stay-pending-and-alive-after-user-owner-is-dropped
  (doseq [backend backends]
    (let [producer ["str" ["anonymous"] "resolve-producer"]
          table (scheduled-functions
                 {producer {:params [1 2]
                            :body [:let 3 [:runtime "lean_io_check_canceled" [[:var 2]]]
                                   [:call 4 [:direct "lean_io_promise_resolve"] [[:imm m/erased] [:var 3] [:var 1] [:var 2]]
                                    [:dec [:var 1] 1 [:return [:imm 0]]]]]}})
          [world p] (new-promise (m/world table)) [world t] (result-task world p)
          [world closure] (task-closure (m/retain world p 1) producer [p])
          spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
          job (:result spawned) dropped (scheduled-call backend spawned "drop" [job])
          after (scheduled-call backend dropped task/get-target [m/erased t])
          option (:result after)]
      (is (= :promise-pending (:task-state (m/node spawned t))))
      (is (= :waiting (:task-state (m/node dropped job))))
      (is (= [job] (get-in dropped [:task-runtime :queue])))
      (is (= 1 (:rc (m/node dropped job))))
      (is (true? (:cancelled? (m/node dropped job))))
      (is (= [1] (:fields (m/node after option))))
      (is (= [] (get-in after [:task-runtime :queue])))
      (is (= [] (get-in after [:task-runtime :active])))
      (is (not (contains? (:heap after) (:id job))))
      (is (empty? (:heap (-> after (m/release option 1) (m/release p 1))))))))

(deftest pending-sync-maps-do-not-force-promises-and-run-on-resolution
  (doseq [backend backends]
    (let [unwrap ["str" ["anonymous"] "unwrap-option"]
          table (scheduled-functions {unwrap {:params [1]
                                              :body [:let 2 [:runtime "lean_option_get_or_block" [[:imm m/erased] [:imm m/erased] [:var 1]]]
                                                     [:return [:var 2]]]}})
          [world p] (new-promise (m/world table)) [world t] (result-task world p)
          [world closure] (task-closure world unwrap [])
          mapped (scheduled-call backend world "lean_task_map" [m/erased m/erased closure t 0 1])
          mapped-task (:result mapped)
          resolved (scheduled-call backend mapped "lean_io_promise_resolve" [m/erased 42 p m/erased])
          read (scheduled-call backend resolved task/get-target [m/erased mapped-task])]
      (is (= :waiting (:task-state (m/node mapped mapped-task))))
      (is (= :promise-pending (:task-state (m/node mapped t))))
      (is (= :ready (:task-state (m/node resolved mapped-task))))
      (is (= 42 (:result read)))
      (is (= [] (get-in read [:task-runtime :queue])))
      (is (empty? (:heap (m/release read p 1)))))))

(deftest pure-spawn-drop-cancels-unstarted-job-and-releases-its-captures
  (doseq [backend backends]
    (let [f ["str" ["anonymous"] "never-run"]
          [world resource] (m/resource (m/world (scheduled-functions {f {:params [1 2] :body [:unreachable]}})) "unstarted")
          [world closure] (task-closure world f [resource])
          spawned (scheduled-call backend world "lean_task_spawn" [m/erased closure 0])
          after (scheduled-call backend spawned "drop" [(:result spawned)])]
      (is (empty? (:heap after)))
      (is (= [[:released "unstarted"]] (:events after)))
      (is (= [] (get-in after [:task-runtime :queue]))))))

(deftest bind-flattens-a-returned-task-through-visible-guest-calls
  (doseq [backend backends]
    (let [f ["str" ["anonymous"] "make-task"]
          table (scheduled-functions {f {:params [1]
                                         :body [:let 2 [:runtime "lean_nat_add" [[:var 1] [:imm 1]]]
                                                [:let 3 [:runtime "lean_task_pure" [[:imm m/erased] [:var 2]]]
                                                 [:return [:var 3]]]]}})
          pure (scheduled-call backend (m/world table) "lean_task_pure" [m/erased 41])
          [world closure] (task-closure pure f [])
          bound (scheduled-call backend world "lean_task_bind" [m/erased m/erased (:result pure) closure 0 1])
          after (scheduled-call backend bound task/get-target [m/erased (:result bound)])]
      (is (= :ready (:task-state (m/node bound (:result bound)))))
      (is (= 42 (:result after)))
      (is (empty? (:heap after)))
      (is (= [] (get-in after [:task-runtime :queue]))))))

(deftest explicit-drain-and-fuel-resumption-preserve-cooperative-jobs
  (doseq [backend backends fuel [0 1 2 3 5 8 13 21 34 55]]
    (let [f ["str" ["anonymous"] "io-result"]
          [world resource] (m/resource (m/world (scheduled-functions {f {:params [1 2] :body [:return [:var 1]]}})) "drain-result")
          [world closure] (task-closure world f [resource])
          spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
          dropped (scheduled-call backend spawned "drop" [(:result spawned)])
          paused (run-state backend (m/start dropped drain-target []) fuel)
          after (if (= :paused (:status paused)) (run-state backend (m/resume paused m/erased) 100000) paused)]
      (is (= :done (:status after)))
      (is (= 0 (:result after)))
      (is (empty? (:heap after)))
      (is (= [[:released "drain-result"]] (:events after)))
      (is (= [] (get-in after [:task-runtime :active]))))))

(deftest baseio-preserves-except-errors-as-task-values
  (doseq [backend backends]
    (let [f ["str" ["anonymous"] "baseio-except-value"]
          [world error] (m/allocate (m/world (scheduled-functions {f {:params [1 2] :body [:return [:var 1]]}})) :ctor 0 ["expected-error"])
          [world closure] (task-closure world f [error])
          spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
          after (scheduled-call backend spawned "lean_io_wait" [m/erased (:result spawned) m/erased])]
      (is (= error (:result after)))
      (is (= 0 (:tag (m/node after error))))
      (is (= ["expected-error"] (:fields (m/node after error))))
      (is (= 1 (:rc (m/node after error)))))))

(deftest wait-any-runs-a-queued-producer-and-preserves-its-borrowed-list
  (doseq [backend backends]
    (let [f ["str" ["anonymous"] "wait-any-producer"]
          table (scheduled-functions {f {:params [1] :body [:return [:imm 42]]}})
          [world closure] (task-closure (m/world table) f [])
          spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
          [world tasks] (m/guest-list spawned [(:result spawned)])
          after (scheduled-call backend world "lean_io_wait_any" [m/erased tasks m/erased m/erased])]
      (is (= 42 (:result after)))
      (is (= 1 (:rc (m/node after tasks))))
      (is (empty? (:heap (m/release after tasks 1)))))))

#?(:clj
   (deftest queued-io-kernel-callbacks-can-invoke-guests-and-fork-host-associations
     (doseq [backend backends]
       (let [f ["str" ["anonymous"] "io-kernel-callback"]
             helper ["str" ["anonymous"] "kernel-root-roundtrip"]
             table (scheduled-functions {f {:params [1 2] :body [:host "kernel-call" [[:var 1] [:var 2]] 3 [:return [:var 3]]]}
                                         helper {:params [1] :body [:return [:var 1]]}})
             [world kernel-root] (m/allocate (m/world table) :ctor 0 [42])
             [world closure] (task-closure world f [kernel-root])
             spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
             job (:result spawned) left-env (ansatz.kernel.Env.) right-env (ansatz.kernel.Env.)
             session (raw/open-functions table
                       {"kernel-call" {:signature {:params [{:ty "object" :borrow false} {:ty "void" :borrow false}] :return-type "object"}
                                       :handler (fn [{:keys [invoke]} state [root world-token]]
                                                  (is (= m/erased world-token))
                                                  (let [[state value] (invoke (m/retain state root 1) helper [root])]
                                                    [(assoc-in state [:kernel-environments value]
                                                               {:anchor value :env (get-in state [:environment :env])}) value]))}}
                       {:backend backend})
             left (raw/call session (assoc spawned :environment {:env left-env}) task/get-target [m/erased job])
             right (raw/call session (assoc spawned :environment {:env right-env}) task/get-target [m/erased job])]
         (is (= kernel-root (:value left)))
         (is (= kernel-root (:value right)))
         (is (identical? left-env (get-in left [:state :kernel-environments kernel-root :env])))
         (is (identical? right-env (get-in right [:state :kernel-environments kernel-root :env])))
         (is (= 2 (:rc (m/node (:state left) kernel-root))))
         (is (= [] (get-in left [:state :task-runtime :queue])))
         (is (= [] (get-in left [:state :task-runtime :active])))
         (is (= :waiting (:task-state (m/node spawned job))))
         (is (nil? (:kernel-environments spawned)))))))

#?(:clj
   (deftest failed-job-retains-a-real-checkpoint-without-publishing-a-result
     (doseq [backend backends]
       (let [f ["str" ["anonymous"] "failing-io-callback"]
             table (scheduled-functions {f {:params [1] :body [:host "kernel-failure" [] 2 [:return [:var 2]]]}})
             [world closure] (task-closure (m/world table) f [])
             spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure 0 m/erased])
             job (:result spawned)
             session (raw/open-functions table
                       {"kernel-failure" {:signature {:params [] :return-type "object"}
                                          :handler (fn [{:keys [checkpoint!]} state _]
                                                     (checkpoint! (assoc-in state [:kernel-environments :checked] :yes))
                                                     (throw (ex-info "kernel rejected" {})))}} {:backend backend})
             error (try (raw/call session spawned task/get-target [m/erased job]) nil
                        (catch clojure.lang.ExceptionInfo e e))
             checkpoint (:checkpoint (ex-data error))]
         (is (= :yes (get-in checkpoint [:kernel-environments :checked])))
         (is (= :running (:task-state (m/node checkpoint job))))
         (is (= [] (:fields (m/node checkpoint job))))
         (is (= [job] (get-in checkpoint [:task-runtime :active])))
         (is (= :waiting (:task-state (m/node spawned job))))
         (is (nil? (:kernel-environments spawned)))))))

#?(:clj
   (deftest isolated-task-root-links-getter-and-sizes-mutable-registers
     (let [entry ["str" ["str" ["anonymous"] "BaseIO"] "asTask"]
           signatures {"lean_io_as_task" [{:params [{:ty "erased" :borrow false} {:ty "object" :borrow false}
                                                   {:ty "tobject" :borrow false} {:ty "void" :borrow false}]
                                          :return-type "object"}]
                       "lean_task_get_own" [{:params [{:ty "erased" :borrow false} {:ty "object" :borrow false}]
                                             :return-type "tobject"}]}
           row (fn [name symbol]
                 (let [shape (first (get signatures symbol))]
                   {:name name :ir {:extern {:f name :xs (mapv #(assoc %1 :x {:idx %2}) (:params shape) (range 1 5))
                                            :type (:return-type shape)
                                            :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}}))
           catalogue {:declarations {entry (row entry "lean_io_as_task") task/get-target (row task/get-target "lean_task_get_own")}
                      :manifests [{:schema "lean-ir-probe/1" :leanVersion "4.33.1"
                                   :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}}]}
           linked (with-redefs [abi/signatures (delay signatures)] (ir/load-closure catalogue [entry] abi/lower))
           f ["str" ["anonymous"] "isolated-io-job"]
           table (assoc linked f {:params [1] :body [:return [:imm 42]]})]
       (is (= #{entry task/get-target} (set (keys linked))))
       (doseq [backend [:mutable :jvm]]
         (let [[world closure] (task-closure (m/world table) f [])
               spawned (scheduled-call backend world entry [m/erased closure 0 m/erased])
               after (scheduled-call backend spawned task/get-target [m/erased (:result spawned)])]
           (is (= 42 (:result after)))
           (is (empty? (:heap after))))))))

(deftest native-priority-and-sync-flags-store-and-execute-semantic-values
  (doseq [backend backends sync [0 1]]
    (let [f ["str" ["anonymous"] "native-sync-map"]
          table (scheduled-functions {f {:params [1] :body [:return [:imm 42]]}})
          pure (scheduled-call backend (m/world table) "lean_task_pure" [m/erased 41])
          [world closure] (task-closure pure f [])
          mapped (scheduled-call backend world "lean_task_map"
                   [m/erased m/erased closure (:result pure) (native/native-scalar 3) (native/native-scalar sync)])
          node (m/node mapped (:result mapped))]
      (is (= 3 (:priority node)))
      (is (= (= 1 sync) (:sync? node)))
      (is (= (if (= 1 sync) :ready :waiting) (:task-state node)))
      (is (= 42 (:result (scheduled-call backend mapped task/get-target [m/erased (:result mapped)])))))))

(deftest native-none-and-list-nil-preserve-pending-and-wait-semantics
  (doseq [backend backends]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Dropped promise result"
          (run-op backend (m/world functions) "lean_option_get_or_block" [m/erased m/erased (native/native-scalar 0)])))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Malformed promise result"
          (run-op backend (m/world functions) "lean_option_get_or_block" [m/erased m/erased (native/native-scalar 1)])))
    (let [f ["str" ["anonymous"] "native-nil-producer"]
          table (scheduled-functions {f {:params [1] :body [:return [:imm 42]]}})
          [world closure] (task-closure (m/world table) f [])
          spawned (scheduled-call backend world "lean_io_as_task" [m/erased closure (native/native-scalar 0) m/erased])
          [world tasks] (m/guest-list spawned [(:result spawned)])
          world (assoc-in world [:heap (:id tasks) :fields 1] (native/native-scalar 0))
          after (scheduled-call backend world "lean_io_wait_any" [m/erased tasks m/erased m/erased])]
      (is (= 42 (:result after)))
      (is (empty? (:heap (m/release after tasks 1)))))))
