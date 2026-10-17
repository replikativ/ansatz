(ns prototype.module-runtime-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.module-runtime :as runtime]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defn- named [catalogue label]
  (first (filter #(= label (ir/name-label %)) (keys (:declarations catalogue)))))

(defn- fixture []
  (let [catalogue (ir/index-bundles ["fixtures/runtime.jsonl"])
        manifest (first (:manifests catalogue))
        root (get-in manifest [:initializationPlan :module])
        init-name ["str" ["anonymous"] "Init"]
        imported (-> manifest
                     (assoc :initializationPlan {:schema "lean-init-plan/1" :module init-name
                                                 :moduleSystem false :imports [] :actions []}))
        catalogue (assoc catalogue :manifests [imported manifest])]
    {:catalogue catalogue :root root :init-name init-name
     :counter (named catalogue "RuntimeProbe.counter")
     :mode (named catalogue "RuntimeProbe.wasInitializing")
     :bump (named catalogue "RuntimeProbe.bump")}))

(deftest ordered-module-actions-use-real-guest-ref-primitives
  (let [{:keys [catalogue root counter mode bump init-name]} (fixture)
        linked (runtime/link catalogue root [bump])]
    (is (= 2 (count (get-in linked [:expanded :actions]))))
    (is (= #{root init-name} (set (keys (:module-plans linked)))))
    (is (every? :runtimeProfile (:manifests catalogue)))
    (doseq [backend [:reference :mutable :jvm]]
      (let [checkpoint (atom nil) observed (atom [])
            _ (add-watch checkpoint ::collect (fn [_ _ _ value] (swap! observed conj value)))
            result (runtime/run linked (m/world (:functions linked)) backend 1000
                                {:checkpoint checkpoint :checkpoint-every 1})
            counter-ref (get-in result [:globals counter :value])]
        (is (= :done (:status result)))
        (is (= [40] (:fields (m/node result counter-ref))))
        (is (= 0 (:rc (m/node result counter-ref))))
        (is (= 1 (get-in result [:globals mode :value])))
        (is (= #{[root :all] [init-name :all]} (:initialized-modules result)))
        (is (not (contains? result :initialization-scope)))
        (is (not (contains? result :initializing?)))
        (is (= [0 1 2 2] (mapv :next-action @observed)))
        (is (:initializing? (:snapshot (first @observed))))
        (is (= result (:snapshot @checkpoint)))
        (testing "guards skip repeated initialization and preserve modified refs"
          (let [bumped (m/run (m/start result bump [m/erased]))
                again (runtime/run linked bumped backend 1000)]
            (is (= [41] (:fields (m/node again counter-ref))))
            (is (= (:heap bumped) (:heap again)))
            (is (= (:stats bumped) (:stats again)))))
        (testing "scope restores an existing explicit initialization flag"
          (let [initial (assoc (m/world (:functions linked)) :initializing? false)
                result (runtime/run linked initial backend 1000)]
            (is (false? (:initializing? result)))))))))

(deftest mutable-backends-reuse-one-machine
  (let [{:keys [catalogue root]} (fixture)
        linked (runtime/link catalogue root [])
        original-thaw u/thaw original-start u/start!]
    (doseq [backend [:mutable :jvm]]
      (let [thaws (atom 0) starts (atom [])]
        (with-redefs [u/thaw (fn [world] (swap! thaws inc) (original-thaw world))
                      u/start! (fn [machine target args]
                                 (swap! starts conj machine)
                                 (original-start machine target args))]
          (runtime/run linked (m/world (:functions linked)) backend 1000))
        (is (= 1 @thaws))
        (is (= 2 (count @starts)))
        (is (identical? (:heap (first @starts)) (:heap (second @starts))))))))

(deftest action-failures-retain-state-and-checkpoint
  (let [{:keys [catalogue root]} (fixture)
        ref-name (named catalogue "ST.Prim.mkRef")
        broken (assoc-in catalogue [:declarations ref-name :ir :extern :ext :entries 0 :standard :fn]
                         "missing_module_runtime_test_primitive")
        linked (runtime/link broken root [])]
    (doseq [backend [:reference :mutable :jvm]]
      (let [checkpoint (atom nil)
            failure (try (runtime/run linked (m/world (:functions linked)) backend 1000
                                      {:checkpoint checkpoint})
                         nil (catch clojure.lang.ExceptionInfo e e))
            data (ex-data failure)]
        (is (some? failure))
        (is (= "missing_module_runtime_test_primitive" (get-in data [:declaration :symbol])))
        (is (= root (get-in data [:module-action :module])))
        (is (:initializing? (:snapshot data)))
        (is (contains? (:snapshot data) :initialization-scope))
        (is (empty? (:initialized-modules (:snapshot data))))
        (is (= 0 (:next-action @checkpoint)))
        (is (= (:checkpoint data) @checkpoint))
        (is (not= (:snapshot data) (:snapshot @checkpoint)))
        (is (:module-initialization-failure (:snapshot data)))
        (is (empty? (:globals (:snapshot @checkpoint))))))))

(deftest budget-failures-preserve-a-resumable-action
  (let [{:keys [catalogue root]} (fixture)
        linked (runtime/link catalogue root [])]
    (doseq [backend [:reference :mutable :jvm]]
      (let [checkpoint (atom nil)
            failure (try (runtime/run linked (m/world (:functions linked)) backend 0
                                      {:checkpoint checkpoint})
                         nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= :paused (get-in (ex-data failure) [:snapshot :status])))
        (is (= 0 (:next-action @checkpoint)))
        (is (:initializing? (:snapshot @checkpoint)))
        (let [ready (runtime/resume linked @checkpoint backend 1000)]
          (is (= :done (:status ready)))
          (is (not (contains? ready :initialization-scope))))))))

(deftest linker-rejects-conflicting-plans
  (let [{:keys [catalogue root]} (fixture)
        manifest (last (:manifests catalogue))
        conflicting (update-in manifest [:initializationPlan :actions] pop)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Conflicting producer"
                         (runtime/link (update catalogue :manifests conj conflicting) root [])))))

(deftest value-and-anonymous-io-actions-run-in-producer-order
  (let [catalogue (ir/index-bundles ["fixtures/source-globals.jsonl"])
        ;; This older fixture predates structured phase-aware import records.
        manifest (assoc-in (first (:manifests catalogue)) [:initializationPlan :imports]
                           [{:module ["str" ["anonymous"] "Init"] :meta false}])
        root (get-in manifest [:initializationPlan :module])
        imported (assoc manifest :initializationPlan
                        {:schema "lean-init-plan/1" :module ["str" ["anonymous"] "Init"]
                         :moduleSystem false :imports [] :actions []})
        catalogue (assoc catalogue :manifests [imported manifest])
        linked (runtime/link catalogue root [])]
    (is (= ["value" "initialize" "io" "initialize" "initialize"]
           (mapv #(get-in % [:action :kind]) (get-in linked [:expanded :actions]))))
    (doseq [backend [:reference :mutable :jvm]]
      (let [world (runtime/run linked (m/world (:functions linked)) backend 1000)]
        (is (= 73 (get-in world [:globals (named catalogue "initializedNat") :value])))
        (is (= 18446744073709551615N
               (get-in world [:globals (named catalogue "initializedWide") :value])))
        (is (= [41 42] (m/list-values world (get-in world [:globals (named catalogue "initializedList") :value]))))))))

(defn- effects-fixture []
  (let [{:keys [catalogue root bump] :as base} (fixture)
        first-action ["str" root "firstEffect"]
        failing-action ["str" root "failingEffect"]
        missing ["str" root "missingImplementation"]
        variable (fn [i] {:var {:id {:idx i}}})
        params [{:x {:idx 1} :ty "void" :borrow false}]
        function-row (fn [name params body]
                       {:kind "decl" :name name :runtime {:role "ordinary"}
                        :ir {:fdecl {:f name :xs params :type "object" :body body}}})
        first-row (function-row first-action params
                                ["vdecl" {:idx 2} "object" {:fap {:c bump :ys ["erased"]}}
                                 ["ret" (variable 2)]])
        failing-row (function-row failing-action params
                                  ["vdecl" {:idx 2} "object" {:fap {:c bump :ys ["erased"]}}
                                   ["dec" {:idx 2} 1 true false
                                    ["vdecl" {:idx 3} "object" {:fap {:c missing :ys []}}
                                     ["ret" (variable 3)]]]])
        missing-row {:kind "decl" :name missing :runtime {:role "ordinary"}
                     :ir {:extern {:f missing :xs [] :type "object"
                                   :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                              :fn "module_checkpoint_missing"}}]}}}}
        fixed-row (function-row missing []
                                ["vdecl" {:idx 0} "object" {:lit {:v {:num {:v 0}}}}
                                 ["vdecl" {:idx 1} "object"
                                  {:ctor {:i {:cidx 0 :size 1 :usize 0 :ssize 0} :ys [(variable 0)]}}
                                  ["ret" (variable 1)]]])
        catalogue (-> catalogue
                      (update :declarations into (map (juxt :name identity) [first-row failing-row missing-row]))
                      (update-in [:manifests 1 :initializationPlan :actions] into
                                 (mapv (fn [name] {:action {:kind "io" :name name :target name} :meta false})
                                       [first-action failing-action])))]
    (assoc base :catalogue catalogue :first-action first-action :failing-action failing-action
           :fixed-catalogue (assoc-in catalogue [:declarations missing] fixed-row))))

(defn- counter-value [world counter]
  (first (:fields (m/node world (get-in world [:globals counter :value])))))

(deftest clean-checkpoint-resume-rolls-back-failed-effects-and-allows-explicit-upgrades
  (let [{:keys [catalogue fixed-catalogue root counter]} (effects-fixture)
        linked (runtime/link catalogue root []) fixed (runtime/link fixed-catalogue root [])]
    (doseq [backend [:reference :mutable :jvm] interval [1 100]]
      (let [checkpoint (atom nil)
            failure (try (runtime/run linked (assoc (m/world (:functions linked)) :initializing? false) backend 1000
                                      {:checkpoint checkpoint :checkpoint-every interval})
                         nil (catch clojure.lang.ExceptionInfo e e))
            partial (:snapshot (ex-data failure)) clean @checkpoint
            other-backend (case backend :reference :jvm :mutable :reference :jvm :mutable)]
        (is (= 3 (:action-index (ex-data failure))))
        (is (= 42 (counter-value partial counter)))
        (is (= clean (:checkpoint (ex-data failure))))
        (is (= (if (= interval 1) 3 0) (:next-action clean)))
        (when (= interval 1) (is (= 41 (counter-value (:snapshot clean) counter))))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"program mismatch"
                             (runtime/resume fixed clean other-backend 1000)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"incomplete"
                             (runtime/run linked partial backend 1000)))
        (let [resumed (runtime/resume fixed clean other-backend 1000
                                      {:allow-program-upgrade true :checkpoint checkpoint})
              expected (runtime/run fixed (m/world (:functions fixed)) :reference 1000)]
          (is (= 42 (counter-value resumed counter)))
          (is (= (:heap expected) (:heap resumed)))
          (is (= (:globals expected) (:globals resumed)))
          (is (= (:stats expected) (:stats resumed)))
          (is (= 4 (:next-action @checkpoint)))
          (is (:complete? @checkpoint))
          (is (not (contains? resumed :initialization-scope)))
          (is (false? (:initializing? resumed)))
          (is (= resumed (runtime/resume fixed @checkpoint backend 1000))))))))

(deftest checkpoint-validation-rejects-different-plans-actions-scope-and-abi
  (let [{:keys [catalogue fixed-catalogue root first-action]} (effects-fixture)
        linked (runtime/link catalogue root [])
        checkpoint (atom nil)
        failure (try (runtime/run linked (m/world (:functions linked)) :reference 1000
                                  {:checkpoint checkpoint :checkpoint-every 1})
                     nil (catch clojure.lang.ExceptionInfo e e))
        clean @checkpoint]
    (doseq [changed [(assoc linked :root-module ["str" ["anonymous"] "differentRoot"])
                     (assoc linked :phase :comptime)
                     (update-in linked [:module-plans root :actions] #(vec (reverse %)))]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"plan/root/phase mismatch"
                           (runtime/resume changed clean :reference 1000))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"action sequence"
                         (runtime/resume linked (update clean :actions #(vec (reverse %))) :reference 1000)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"scope"
                         (runtime/resume linked (update clean :snapshot dissoc :initialization-scope) :reference 1000)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"scope"
                         (runtime/resume linked (assoc-in clean [:snapshot :initialization-scope :heap] {}) :reference 1000)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Failed partial"
                         (runtime/resume linked (assoc clean :snapshot (:snapshot (ex-data failure))) :reference 1000)))
    (let [changed-abi (runtime/link (assoc-in fixed-catalogue [:declarations first-action :ir :fdecl :xs 0 :borrow] true)
                                    root [])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"declaration ABI"
                           (runtime/resume changed-abi clean :reference 1000 {:allow-program-upgrade true}))))
    (let [changed-profile (assoc (runtime/link fixed-catalogue root []) :runtime-profiles #{:different})]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"runtime ABI"
                           (runtime/resume changed-profile clean :reference 1000 {:allow-program-upgrade true}))))
    (let [changed-arity (update-in (runtime/link fixed-catalogue root []) [:functions first-action :params] conj 99)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"declaration ABI"
                           (runtime/resume changed-arity clean :reference 1000 {:allow-program-upgrade true}))))))

(deftest extending-modules-preserves-existing-code-globals-and-once-guards
  (let [{:keys [catalogue root counter bump]} (fixture)
        linked (runtime/link catalogue root [bump])
        old (runtime/run linked (m/world (:functions linked)) :reference 1000)
        old (m/run (m/start old bump [m/erased]))
        added-root ["str" ["anonymous"] "AddedModule"]
        added-value ["str" ["anonymous"] "addedValue"]
        row {:kind "decl" :name added-value :runtime {:role "value"}
             :ir {:fdecl {:f added-value :xs [] :type "tobject"
                          :body ["vdecl" {:idx 0} "tobject" {:lit {:v {:num {:v 7}}}}
                                 ["ret" {:var {:id {:idx 0}}}]]}}}
        manifest (assoc (first (:manifests catalogue))
                   :initializationPlan {:schema "lean-init-plan/1" :module added-root :moduleSystem false
                                        :imports [{:module root :meta false}]
                                        :actions [{:meta false :action {:kind "value" :name added-value :target added-value}}]})
        catalogue (-> catalogue (update :manifests conj manifest) (assoc-in [:declarations added-value] row))
        reads (atom [])
        extended (runtime/link catalogue added-root []
                   {:initialized-modules (:initialized-modules old)
                    :existing-functions (:functions old) :existing-program-abi (:program-abi linked)
                    :lower (fn [row] (swap! reads conj (:name row)) (ir/lower-declaration row))})]
    (is (= [added-value] @reads))
    (is (= 1 (count (get-in extended [:expanded :actions]))))
    (is (every? (fn [[n f]] (identical? f (get-in extended [:functions n]))) (:functions old)))
    (doseq [backend [:reference :mutable :jvm]]
      (let [checkpoint (atom nil)
            world (runtime/run extended (assoc old :functions (:functions extended)) backend 1000 {:checkpoint checkpoint})]
        (is (= 41 (counter-value world counter)))
        (is (= 7 (get-in world [:globals added-value :value])))
        (is (contains? (:initialized-modules world) [added-root :all]))
        (is (= world (runtime/resume extended @checkpoint backend 1000)))))))
