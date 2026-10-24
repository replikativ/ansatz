(ns prototype.project-failure-disposal-test
  "Actual Context ownership, explicitly modeled compiler/Project child transport."
  (:require [clojure.test :refer [deftest is]]
            [prototype.project-loader :as project]
            [prototype.project-loader-test :as model]
            [prototype.project-discovery-test :as files]
            [prototype.source-graph-runtime-test :as fixture]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as graph])
  (:import [ansatz.kernel Name]
           [java.lang.ref WeakReference]
           [java.util WeakHashMap]))

(defn failure-token [cause] (:project-failure-diagnostic (ex-data cause)))
(defn ledger [token]
  (let [registry @#'project/failures]
    (locking registry (.get ^WeakHashMap registry token))))
(defn closed? [context] (some? (model/thrown #(resident/snapshot context))))
(defn with-project [backend f]
  (files/with-files {["A"] (files/text "A") ["D"] (files/text "D")}
    (fn [_ provider]
      (fixture/with-empty-publication backend
        (fn [{:keys [context] :as data}]
          (let [owner (project/open-project context (model/options data provider))]
            (try (f owner context)
                 (finally (project/close-project! owner)))))
        :configure (files/configure (atom {(files/text "A") {:deps []}
                                          (files/text "D") {:deps []}}))))))

(deftest construction-failure-disposes-only-created-private-wrapper
  (doseq [backend [:reference :mutable :jvm]]
    (files/with-files {["A"] (files/text "A")}
      (fn [_ provider]
        (fixture/with-empty-publication backend
          (fn [{:keys [context] :as data}]
            (let [before (resident/snapshot context) forks (atom []) actual resident/fork
                  selected (ex-info "second fork fails" {})
                  cause (with-redefs [resident/fork
                                      (fn [input]
                                        (if (seq @forks) (throw selected)
                                          (let [child (actual input)] (swap! forks conj child) child)))]
                          (model/thrown #(project/open-project context (model/options data provider))))
                  token (failure-token cause)]
              (is (identical? selected (.getCause ^Throwable cause)))
              (is (= 1 (count @forks)))
              (is (= :construction (:operation (project/dispose-failure! token))))
              (is (every? closed? @forks))
              (is (identical? before (resident/snapshot context)))))
          :configure (files/configure (atom {(files/text "A") {:deps []}})))))))

(deftest preparation-failure-capsule-retires-unissued-load-owners
  (doseq [backend [:reference :mutable :jvm]]
    (with-project backend
      (fn [owner parent]
        (let [before (resident/snapshot parent)
              ;; Valid captured module, deliberately missing explicit export record.
              cause (model/thrown #(project/prepare-load owner
                                    {:roots [(files/wire ["A"])] :exports []}))
              token (failure-token cause) state (ledger token) owned (:owned @state)
              receipt (project/dispose-failure! token)]
          (is (= 2 (count owned)))
          (is (= :load (:operation receipt)))
          (is (identical? receipt (project/dispose-failure! token)))
          (is (= #{:phase :disposal} (set (keys @state))))
          (is (every? closed? owned))
          (is (identical? before (resident/snapshot parent)))
          (is (.contains (.getMessage ^Throwable cause) "exactly the captured")))))))

(deftest load-and-capsule-aliases-share-disposal-in-both-orders
  (doseq [backend [:reference :mutable :jvm] first-api [:capsule :load] mode [:graph :native]]
    (with-project backend
      (fn [owner parent]
        (let [before (resident/snapshot parent) disposal-calls (atom [])
              models (assoc (model/protocol-models (atom []) (atom []))
                            #'graph/dispose-source-graph-import!
                            (fn [control] (swap! disposal-calls conj [:graph control]))
                            #'graph/dispose-native-init-base!
                            (fn [control] (swap! disposal-calls conj [:native control])))
              request {:roots (if (= mode :native) [(files/wire ["A"]) (files/wire ["D"])]
                                 [(files/wire ["A"])])
                       :exports (model/exports (if (= mode :native) ["A" "D"] ["A"]))}
              prepared (with-redefs-fn models #(project/prepare-load owner request))
              control (:control prepared) selected (ex-info "observer selected" {})
              cause (with-redefs-fn models
                      #(model/thrown
                         (fn []
                           (loop []
                             (project/advance-load! control
                               {:max-operations 1 :wall-ms 1000
                                :observe! (fn [progress]
                                            (when (= :child-finish (:phase progress))
                                              (throw selected)))})
                             (recur)))))
              token (failure-token cause) state (ledger token) saved @state owned (:owned saved)
              live (.get ^WeakReference (:live-state saved))
              _ (is (identical? live (#'project/load-state! control)))
              _ (is (identical? cause (model/thrown #(project/finish-load! control))))
              _ (is (empty? @disposal-calls))
              receipt (with-redefs-fn models
                        #(if (= :capsule first-api) (project/dispose-failure! token)
                           (project/dispose-load! control)))]
          (is (identical? selected (.getCause ^Throwable cause)))
          (is (= [[mode (:child saved)]] @disposal-calls))
          (is (identical? receipt (project/dispose-failure! token)))
          (is (identical? receipt (project/dispose-load! control)))
          (is (= #{:phase :disposal} (set (keys @state)) (set (keys @live))))
          (is (every? closed? owned))
          (is (identical? before (resident/snapshot parent)))
          (is (some? (model/thrown #(project/advance-load! control {:max-operations 1 :wall-ms 100}))))
          (is (some? (model/thrown #(project/finish-load! control))))
          ;; Original caller diagnostics remain intact after library retirement.
          (is (identical? token (failure-token cause)))
          (is (map? (:project-load-state (ex-data cause)))))))))

(deftest invocation-failure-capsule-leaves-successful-parent-live
  (doseq [backend [:reference :mutable :jvm] operation [:invoke :invoke-io]]
    (with-project backend
      (fn [owner parent]
        (let [models (model/protocol-models (atom []) (atom []))
              loaded (with-redefs-fn models
                       #(project/load-file owner {:module (files/wire ["A"]) :exports (model/exports ["A"])}
                          {:max-operations 1 :wall-ms 1000}))
              version (:project loaded) selected (ex-info "selected call failed" {})
              operation-fn (if (= :invoke operation) project/invoke project/invoke-io)]
          (try
            (let [cause (with-redefs [resident/call (fn [& _] (throw selected))
                                     resident/call-io (fn [& _] (throw selected))]
                          (model/thrown #(operation-fn version (files/wire ["A"])
                                           (Name/fromString "A.answer") [41] {:arguments [:nat] :result :nat})))
                  token (failure-token cause) state (ledger token) owned (:owned @state)]
              (is (identical? selected (.getCause ^Throwable cause)))
              (is (= 2 (count owned)))
              (is (= operation (:operation (project/dispose-failure! token))))
              (is (every? closed? owned))
              (is (map? (resident/snapshot parent)))
              (let [called (with-redefs [resident/call (fn [context & _] {:context (resident/fork context) :value 42})]
                             (project/invoke version (files/wire ["A"]) (Name/fromString "A.answer")
                               [41] {:arguments [:nat] :result :nat}))]
                (is (= 42 (:value called))) (project/close-project! (:project called))))
            (finally (project/close-project! version))))))))

(deftest foreign-forged-and-active-controls-do-not-grant-disposal
  (doseq [token [nil {} (project/->ProjectFailure) (project/->ProjectLoad)]]
    (is (some? (model/thrown #(project/dispose-failure! token)))))
  (with-project :reference
    (fn [owner _]
      (let [prepared (project/prepare-load owner {:roots [(files/wire ["A"])] :exports (model/exports ["A"])})
            control (:control prepared) state (#'project/load-state! control)]
        (is (some? (model/thrown #(project/dispose-load! control))))
        (is (= :module-base (:phase @state)))
        ;; This test owns the still-active branch; retire only after explicitly
        ;; making a modeled terminal controller failure, not via cancel semantics.
        (let [selected (ex-info "test terminal failure" {})
              cause (model/thrown #(#'project/failed! state selected))]
          (project/dispose-failure! (failure-token cause)))))))

(deftest disposal-failure-is-terminal-and-keeps-pending-owner-evidence
  (with-project :reference
    (fn [owner parent]
      (let [cause (model/thrown #(project/prepare-load owner {:roots [(files/wire ["A"])] :exports []}))
            token (failure-token cause) state (ledger token) owned (:owned @state)
            selected (ex-info "selected disposal failure" {}) calls (atom 0)]
        (try
          (is (identical? selected
                 (with-redefs [resident/abandon! (fn [_] (swap! calls inc) (throw selected))]
                   (model/thrown #(project/dispose-failure! token)))))
          (is (= :disposal-failed (:phase @state)))
          (is (every? true? (map identical? owned (:owned @state))))
          (is (nil? (:failure @state)))
          (is (some? (model/thrown #(project/dispose-failure! token))))
          (is (= 1 @calls))
          (is (map? (resident/snapshot parent)))
          (finally (doseq [context owned] (resident/abandon! context))))))))
