(ns prototype.coherent-jvm-slice-test
  "Pure model prerequisites; no genuine source load, restore, checking or native resources."
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-consumer-profile :as profile]
            [prototype.coherent-consumer-profile-test :as old]
            [prototype.coherent-stage-guards :as guards]))

(defn name-of [s] ["str" ["anonymous"] s])
(def application
  {:execution-roles profile/execution-roles :transition [:mutable :jvm] :selection-limits profile/selection-limits
   :corpus [{:id "scalar" :module (name-of "Slice") :source-a-id "fixtures/a.lean" :source-b-id "fixtures/b.lean"
             :entry (name-of "entry") :worker (name-of "worker")
             :signature {:arguments [:uint64] :result :uint64}
             :calls [{:args [10] :expected-a 55 :expected-b 65}]
             :fallback {:entry (name-of "fallback") :signature {:arguments [:nat] :result :nat} :args [4] :expected 4}}]
   :callback {:symbol "slice_host_length" :entry (name-of "callback")
              :signature {:params [{:ty "object" :borrow false}] :return-type "tobject"}
              :arguments [{:codec :string :ownership :owned}] :result :nat
              :input "hello" :expected 5 :implementation :utf8-length}})
(defn contract []
  (-> (old/contract-for old/inventory)
      (assoc :profile profile/jvm-profile-id :schema profile/jvm-schema)
      (assoc-in [:composition :stages] profile/jvm-stages)
      (assoc-in [:composition :application] application)))

(deftest explicit-new-profile-retains-legacy-profile-behavior
  (let [new (contract) old (old/contract-for old/inventory)]
    (is (= old (profile/validate-contract! old (:implementation-sha256 old))))
    (is (= new (profile/validate-jvm-contract! new (:implementation-sha256 new))))
    (is (thrown? clojure.lang.ExceptionInfo (profile/validate-contract! new (:implementation-sha256 new))))
    (is (thrown? clojure.lang.ExceptionInfo (profile/validate-jvm-contract! old (:implementation-sha256 old))))))

(deftest exact-stages-never-pretend-a-direct-load-is-project-publication
  (is (= (subvec profile/jvm-stages 0 9)
         (guards/profile-stage-prefix! profile/jvm-profile-id profile/jvm-stages true)))
  (doseq [stages [(assoc profile/jvm-stages 8 :project) (pop profile/jvm-stages)
                  (conj profile/jvm-stages :project) (assoc profile/jvm-stages 11 :select-a)]]
    (is (thrown? clojure.lang.ExceptionInfo (guards/profile-stage-prefix! profile/jvm-profile-id stages true))))
  (is (thrown? clojure.lang.ExceptionInfo (guards/profile-stage-prefix! profile/jvm-profile-id profile/jvm-stages false))))

(deftest finite-policy-bounds-and-host-capability-shapes-fail-closed
  (doseq [bad [(assoc application :transition [:mutable :reference])
               (assoc-in application [:execution-roles :frontend :backend] :jvm)
               (assoc-in application [:selection-limits :max-source-bytes] 1000000)
               (assoc application :corpus (vec (repeat 5 (first (:corpus application)))))
               (assoc-in application [:corpus 0 :source-b-id] "../escape.lean")
               (assoc-in application [:corpus 0 :calls 0 :args] [1 2])
               (assoc-in application [:callback :expected] 9)
               (assoc-in application [:callback :implementation] :arbitrary)
               (assoc-in application [:callback :arguments 0 :ownership] :borrowed)]]
    (is (thrown? clojure.lang.ExceptionInfo (profile/validate-application! bad)))))

(deftest public-reopen-uses-independent-model-configuration-and-retains-input
  (require 'prototype.resident-frontend-test 'prototype.hosted-file-test 'prototype.coherent-jvm-slice)
  (let [prepared ((ns-resolve 'prototype.resident-frontend-test 'prepared) :mutable true
                  @@(ns-resolve 'prototype.hosted-file-test 'captured))
        independent {:trusted-functions (get-in prepared [:world :functions])
                     :trusted-bindings (get-in prepared [:session :bindings])}
        adopt (ns-resolve 'prototype.resident-frontend 'adopt-prepared)
        snapshot (ns-resolve 'prototype.resident-frontend 'snapshot)
        close (ns-resolve 'prototype.resident-frontend 'close!)
        reopen (ns-resolve 'prototype.coherent-jvm-slice 'reopen-application)
        context (adopt prepared independent) before (snapshot context)]
    (try
      (let [compiled (reopen context independent (:application profile/execution-roles))]
        (try
          (is (= :jvm (get-in (snapshot compiled) [:session :backend])))
          (is (= before (snapshot context)))
          (is (identical? (get-in before [:world :functions]) (get-in (snapshot compiled) [:world :functions])))
          (is (thrown? clojure.lang.ExceptionInfo (reopen compiled independent (:application profile/execution-roles))))
          (finally (close compiled))))
      (is (thrown? clojure.lang.ExceptionInfo (reopen context (assoc independent :trusted-bindings {"forged" {}})
                                                     (:application profile/execution-roles))))
      (finally (close context)))))

(deftest returned-owner-is-escrowed-before-its-observer-can-fail
  (let [ns 'prototype.coherent-jvm-slice
        ownership-var (ns-resolve ns 'ownership) call (ns-resolve ns 'owned-call!)
        owner (Object.) ledger (atom {:phase :ready})]
    (with-redefs-fn {ownership-var ledger}
      #(do
         (is (thrown-with-msg? clojure.lang.ExceptionInfo #"observer"
               (call :owner-return (fn [] owner)
                     (fn [value] (is (identical? owner value)) (throw (ex-info "observer" {}))))))
         (is (identical? owner (get-in @ledger [:returned-operation :result])))
         (is (:unsafe-partial? @ledger))
         (is (thrown? clojure.lang.ExceptionInfo
               (prototype.coherent-owner-ledger/begin-disposal! ledger)))))))

(deftest prefix-branches-close-before-source-and-failed-close-is-never-retried
  (let [ns 'prototype.coherent-jvm-slice
        ownership-var (ns-resolve ns 'ownership) dispose (ns-resolve ns 'dispose!)
        close-var (ns-resolve 'prototype.resident-frontend 'close!)
        release-var (ns-resolve 'prototype.resident-init-prefix 'release-prefix)]
    (doseq [fail? [false true]]
      (let [events (atom []) calls (atom 0) context (Object.) released (Object.)
            ledger (atom {:phase :adopted :contexts [{:context context :prefix :model-prefix :closed? false}]
                          :lease (reify java.io.Closeable (close [_] (swap! events conj :source-close)))})]
        (with-redefs-fn {ownership-var ledger
                        release-var (fn [ctx p] (is (identical? context ctx)) (is (= :model-prefix p))
                                      (swap! events conj :prefix-release) {:context released})
                        close-var (fn [ctx]
                                    (swap! calls inc)
                                    (swap! events conj (if (identical? ctx released) :released-context-close :original-context-close))
                                    (when fail? (throw (ex-info "destructive close failed" {}))))}
          #(if fail?
             (do
               (is (thrown? clojure.lang.ExceptionInfo (dispose)))
               (is (thrown? clojure.lang.ExceptionInfo (dispose)))
               (is (= 1 @calls))
               (is (= [:prefix-release :released-context-close] @events))
               (is (:unsafe-partial? @ledger)))
             (do
               (is (= {:disposal-phase :disposed} (dispose)))
               (is (= {:disposal-phase :disposed} (dispose)))
               (is (= [:prefix-release :released-context-close :original-context-close :source-close] @events)))))))))

(deftest explicit-application-cache-is-shared-without-changing-pristine-model-input
  (let [prepared ((ns-resolve 'prototype.resident-frontend-test 'prepared) :mutable true
                  @@(ns-resolve 'prototype.hosted-file-test 'captured))
        independent {:trusted-functions (get-in prepared [:world :functions]) :trusted-bindings {}}
        adopt (ns-resolve 'prototype.resident-frontend 'adopt-prepared)
        snapshot (ns-resolve 'prototype.resident-frontend 'snapshot)
        close (ns-resolve 'prototype.resident-frontend 'close!)
        reopen (ns-resolve 'prototype.coherent-jvm-slice 'reopen-application)
        base (adopt prepared independent) before (snapshot base) shared (prototype.lazy-runtime/code-cache)]
    (try
      (let [a (reopen base independent (:application profile/execution-roles) shared)
            b (reopen base independent (:application profile/execution-roles) shared)]
        (try
          (is (identical? shared (get-in (snapshot a) [:session :cache])))
          (is (identical? shared (get-in (snapshot b) [:session :cache])))
          (is (identical? before (snapshot base)))
          (is (not (identical? shared (get-in before [:session :cache]))))
          (finally (close b) (close a))))
      (finally (close base)))))

(deftest b-load-preserves-existing-callback-effect-and-requires-empty-initializers
  (let [ns 'prototype.coherent-jvm-slice state-var (ns-resolve ns 'state)
        owner-var (ns-resolve ns 'ownership) read-var (ns-resolve ns 'read-input)
        load (ns-resolve ns 'load-version!)
        snapshot-var (ns-resolve 'prototype.resident-frontend 'snapshot)
        load-var (ns-resolve 'prototype.resident-frontend 'load-source)
        base (Object.) child (Object.) file (Object.)
        before {:world {:eval-const-authorizations {:units {}}}}]
    (doseq [initialization? [false true] effect? [false true]]
      (let [state (atom {:bootstrap {} :effects ["already-called"] :pristine-context base
                         :application application :prefix-result {:prefix :model-prefix}})
            ledger (atom {:phase :adopted})
            after {:world {:eval-const-authorizations {:units {old/a {:manifest {:initializationPlan {:actions (if initialization? [:required] [])}}}}}}}]
        (with-redefs-fn {state-var state owner-var ledger read-var (fn [& _] (.getBytes "source-B" "UTF-8"))
                        snapshot-var (fn [ctx] (if (identical? ctx base) before after))
                        load-var (fn [ctx request]
                                   (is (identical? base ctx)) (is (= :defer (:initialization request)))
                                   (when effect? (swap! state update :effects conj "forbidden-load-effect"))
                                   {:success true :context child :file file})}
          #(if (or initialization? effect?)
             (do (is (thrown? clojure.lang.ExceptionInfo (load (first (:corpus application)) :b true)))
                 (is (identical? child (get-in @ledger [:contexts 0 :context]))))
             (do (is (:success (load (first (:corpus application)) :b true)))
                 (is (= ["already-called"] (:effects @state)))
                 (is (identical? child (get-in @ledger [:contexts 0 :context]))))))))))

(deftest new-factory-constructor-is-an-explicit-independent-revision
  (let [issue-var (ns-resolve 'prototype.globals-consumer-factory 'issue-factory*)
        constructor (ns-resolve 'prototype.globals-consumer-factory 'make-coherent-jvm-application-factory)
        seen (atom [])]
    (with-redefs-fn {issue-var (fn [& args] (swap! seen conj args) :model-factory)}
      #(do (is (= :model-factory (constructor {:explicit :options})))
           (is (= :model-factory (constructor {:explicit :options})))) )
    (is (= [true true true true true :coherent-jvm {:explicit :options}] (vec (butlast (first @seen)))))
    (is (not (identical? (last (first @seen)) (last (second @seen)))))))

(deftest restore-envelopes-bind-the-new-profile-and-exact-contract-digest
  (let [check-profile (ns-resolve 'prototype.restore-consumer 'factory-profile!)
        check-result (ns-resolve 'prototype.restore-consumer 'factory-result!)
        producer {:model :producer} description {:producer-preparation producer :consumer-implementation-sha256 old/a
                                                :compatibility-profile profile/jvm-profile-id :consumer-contract-sha256 old/b}
        result (assoc description :catalogue {} :bindings {}) manifest {:binding-signatures {}}]
    (is (= profile/jvm-profile-id (check-profile description producer old/a)))
    (is (= result (check-result result producer old/a profile/jvm-profile-id manifest description)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (check-profile (dissoc description :consumer-contract-sha256) producer old/a)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (check-result (assoc result :consumer-contract-sha256 old/a) producer old/a profile/jvm-profile-id manifest description)))))

(deftest source-preparation-dispatches-the-actual-factory-profile-without-project
  (let [space 'prototype.coherent-source-preparation
        roots @(ns-resolve space 'helper-entrypoint-roots)
        label (ns-resolve space 'lean-name-label)
        controller-resource @(ns-resolve space 'controller-resource)
        entries @(ns-resolve space 'controller-entrypoints)
        contract {:profile profile/jvm-profile-id
                  :composition {:stages profile/jvm-stages
                                :controllers [{:id controller-resource :entrypoints entries}]
                                :helpers (mapv (fn [[id names]] {:id id :entrypoints (mapv label names)}) roots)}}]
    (with-redefs-fn {(ns-resolve 'prototype.globals-consumer-factory 'coherent-contract) (fn [_] {:sha256 old/a :contract contract})
                    (ns-resolve 'prototype.globals-consumer-factory 'descriptor) (fn [_] {:consumer-contract-sha256 old/a})}
      #(let [summary ((ns-resolve space 'validate-approved-composition!) :model-factory)]
         (is (:typed-eio? summary))
         (is (= 9 (count (:required-helper-roles summary))))))))
