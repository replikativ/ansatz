(ns prototype.resident-artifact-test
  "Resident adoption/orchestration MODEL with actual provider-issued artifact
   authority and small captured frontend IR. This does not claim full Init or
   genuine Lean compilation acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-frontend :as resident]
            [prototype.resident-preparation :as preparation]
            [prototype.hosted-file-test :as hosted-model]
            [prototype.artifact-association-test :as artifact-model]
            [prototype.kernel-artifact :as artifact]
            [prototype.kernel-projection-snapshot :as projection]
            [prototype.module-import :as imports]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.guest-encoding :as encoding]))

(defn fixture
  ([] (fixture :reference))
  ([backend]
   (let [hosted (hosted-model/prepared backend true @hosted-model/captured)
         ;; Actual runtime getters follow the bounded model Environment layout.
         root {:params [1] :body [:let 2 [:project [:var 1] 0]
                                 [:inc [:var 2] 1 [:return [:var 2]]]]}
         constants {:params [1] :body [:let 2 [:project [:var 1] 0]
                                      [:let 3 [:project [:var 2] 0]
                                       [:inc [:var 3] 1 [:return [:var 3]]]]]}
         functions (merge (get-in hosted [:world :functions])
                          {(:root imports/helpers) root
                           (:constant-map imports/helpers) constants
                           (:constants imports/helpers) constants
                           (:quot-init? imports/helpers) {:params [1] :body [:return [:imm 1]]}})
         admitted (artifact/load-admitted (assoc (:world hosted) :functions functions)
                                           artifact/native17-profile "fixtures/imported-kernel-native.jsonl")
         projection (artifact/inspect-for-world (:world admitted) (:admission admitted))
         [world environment] (artifact-model/environment (:world admitted) (vec (vals (:constants projection))))
         session (raw/open-functions functions {} {:backend backend :fuel 1000000})
         active (atom session)
         context {:trusted-functions functions :bindings {} :trusted-bindings {}
                  :invoke (fn [world target args]
                            (let [called (raw/call @active world target args)]
                              (reset! active (:session called)) [(:state called) (:value called)]))}
         world (artifact/associate-admitted-progress context world environment imports/helpers (:admission admitted))
         options (:options hosted)
         world (-> world (assoc :result 0)
                   (assoc-in [:globals preparation/options-empty] {:status :ready :value options})
                   (m/retain options 1))
         prepared (assoc hosted :world world :session @active :environment environment)
         configuration {:catalogue (:catalogue prepared) :trusted-functions functions :trusted-bindings {}}]
     {:prepared prepared :candidate (dissoc prepared :options) :configuration configuration
      :admission (:admission admitted) :source (:source admitted) :projection projection})))
(defn with-fixture [f]
  (let [fixture (fixture)]
    (try (f fixture) (finally (.close ^java.io.Closeable (:source fixture))))))
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo error error)))
(defn rc [world value] (:rc (m/node world value)))

(deftest explicit-admitted-adoption-and-preparation-retain-the-actual-mode
  (with-fixture
    (fn [{:keys [prepared candidate configuration admission source]}]
      (let [direct (resident/adopt-admitted prepared configuration admission)
            opened (preparation/open-admitted candidate configuration admission)
            p (resident/snapshot opened)
            branch (resident/fork direct)
            reopened (resident/adopt-like branch (resident/snapshot branch) configuration)
            later (resident/adopter direct)]
        (is (= (inc (rc (:world candidate) (:options prepared))) (rc (:world p) (:options p))))
        (let [root (first (:fields (m/node (:world p) (:environment p))))]
          (is (identical? admission (get-in p [:world :kernel-environments (:id root)
                                              :kernel-provenance :artifact-admission]))))
        (is (thrown-with-msg? Exception #"artifact"
              (resident/adopt-prepared (resident/snapshot reopened) configuration)))
        (resident/close! direct)
        (is (thrown-with-msg? Exception #"closed"
              (resident/adopt-like direct prepared configuration)))
        ;; Captured policy holds only mode/token, and rechecks a fresh boundary.
        (let [after-close (later prepared configuration)]
          (is (some? (resident/snapshot after-close)))
          (resident/close! after-close))
        (doseq [context [opened branch reopened]] (resident/close! context))
        (is (false? @(:closed source)))))))

(deftest strict-entry-points-and-caller-mode-flags-cannot-select-artifact-trust
  (with-fixture
    (fn [{:keys [prepared candidate configuration admission]}]
      (doseq [candidate [(assoc prepared :basis :trusted-artifact :artifact-admission admission)
                         (assoc prepared :kernel-provenance {:base-basis :strict-fresh})]]
        (is (thrown-with-msg? Exception #"artifact" (resident/adopt-prepared candidate configuration))))
      (is (thrown-with-msg? Exception #"artifact" (preparation/open-checked candidate configuration)))
      (is (thrown-with-msg? Exception #"issued in-process"
            (resident/adopt-admitted prepared configuration {:artifact-admission admission}))))))

(deftest admitted-entry-still-requires-independent-readiness-before-association-or-options
  (with-fixture
    (fn [{:keys [candidate configuration admission]}]
      (let [associations (atom 0) acquisitions (atom 0)]
        (with-redefs [resident/resolve-admitted-association
                      (fn [& _] (swap! associations inc) (throw (ex-info "Should not resolve" {})))
                      m/initialized-value (fn [& _] (swap! acquisitions inc))]
          (doseq [bad [(update configuration :trusted-functions dissoc encoding/names-helper)
                       (assoc configuration :trusted-bindings {"foreign" {}})]]
            (let [error (failure #(preparation/open-admitted candidate bad admission))]
              (is (some? error))
              (is (identical? (:world candidate) (:checkpoint (ex-data error))))
              (is (nil? (:resident-preparation-options-entry (ex-data error)))))))
        (is (zero? @associations))
        (is (zero? @acquisitions))))))

(deftest wrong-token-or-source-view-never-acquires-options
  (with-fixture
    (fn [{:keys [prepared candidate configuration admission]}]
      (let [other (artifact/load-admitted (:world prepared) artifact/native17-profile
                                          "fixtures/imported-kernel-native.jsonl")
            acquisitions (atom 0)]
        (try
          (with-redefs [m/initialized-value (fn [& _] (swap! acquisitions inc))]
            (is (thrown-with-msg? Exception #"same issued artifact"
                  (preparation/open-admitted (assoc candidate :world (:world other)) configuration (:admission other))))
            (is (thrown-with-msg? Exception #"absent, duplicated, overlapping or shadowed"
                  (preparation/open-admitted (update candidate :world dissoc :native-imports) configuration admission))))
          (is (zero? @acquisitions))
          (finally (.close ^java.io.Closeable (:source other))))))))

(deftest admitted-load-call-fork-and-session-branches-do-not-repeat-full-java-audits
  (with-fixture
    (fn [{:keys [prepared configuration admission]}]
      (let [base (resident/adopt-admitted prepared configuration admission)]
        (try
          (with-redefs [artifact/inspect-for-world (fn [& _] (throw (ex-info "Hot path repeated issuer audit" {})))
                        projection/validate-segments (fn [& _] (throw (ex-info "Hot path repeated base Java audit" {})))]
            (let [branch (resident/fork base)
                  compiler (resident/with-compiler-options branch {})
                  externs (resident/with-externs compiler {})
                  loaded (resident/load-source externs (hosted-model/request :run))
                  active (:context loaded)
                  called (resident/call active (:file loaded) hosted-model/answer-name [nil 42]
                                        {:arguments [:erased :nat] :result :nat})]
              (is (:success loaded))
              (is (= 42 (:value called)))
              (is (identical? (get-in prepared [:session :cache])
                              (get-in (resident/snapshot (:context called)) [:session :cache])))
              (doseq [context [branch compiler externs active (:context called)]] (resident/close! context))))
          (finally (resident/close! base)))))))

(deftest closed-store-invalidates-operations-but-context-close-does-not-own-the-store
  (with-fixture
    (fn [{:keys [prepared configuration admission source]}]
      (let [base (resident/adopt-admitted prepared configuration admission)
            branch (resident/fork base)]
        (resident/close! base)
        (is (false? @(:closed source)))
        (.close ^java.io.Closeable source)
        (is (thrown-with-msg? Exception #"source lease changed" (resident/fork branch)))
        (resident/close! branch)))))

(deftest second-admitted-association-failure-preserves-the-options-owned-entry
  (with-fixture
    (fn [{:keys [candidate prepared configuration admission source]}]
      (let [resolve resident/resolve-admitted-association calls (atom 0) latest (atom nil)
            error (with-redefs [resident/resolve-admitted-association
                                (fn [context world environment helpers token]
                                  (if (= 1 (swap! calls inc))
                                    (resolve context world environment helpers token)
                                    (let [world (assoc world :resident-artifact-latest true)
                                          session (raw/open-functions (:functions world) {} {:backend :reference})]
                                      (reset! latest {:world world :session session})
                                      (throw (ex-info "injected second admitted association failure"
                                                      {:checkpoint world :checkpoint-session session})))))]
                    (failure #(preparation/open-admitted candidate configuration admission)))
            packet (ex-data error)
            owned (:resident-preparation-options-entry packet)]
        (is (= 2 @calls))
        (is (identical? (:world @latest) (:checkpoint packet)))
        (is (identical? (:session @latest) (:checkpoint-session packet)))
        (is (= owned (:resident-adoption-entry packet)))
        (is (= (inc (rc (:world candidate) (:options prepared)))
               (rc (:world owned) (:options owned))))
        (is (not (:resident-artifact-latest (:world owned))))
        (is (false? @(:closed source)))))))

(deftest selected-application-world-cannot-change-the-context-environment-before-execution
  (with-fixture
    (fn [{:keys [prepared configuration admission]}]
      (let [base (resident/adopt-admitted prepared configuration admission)
            loaded (resident/load-source base (hosted-model/request :run))
            active (:context loaded) effects (atom 0)
            error (failure
                   #(resident/call-with-executor
                     active (:file loaded) hosted-model/answer-name [nil 42]
                     {:arguments [:erased :nat] :result :nat}
                     (fn [{:keys [prepared]}]
                       {:prepared (assoc-in prepared [:world :heap (:id (:environment prepared)) :fields 0]
                                            (m/->Ref -1))
                        :invoke (fn [& _] (swap! effects inc) (throw (ex-info "Must not execute" {})))})))]
        (is (some? error))
        (is (re-find #"kernel lineage" (.getMessage error)))
        (is (zero? @effects))
        (resident/close! active)
        (resident/close! base)))))

(deftest completed-application-does-not-overwrite-a-later-lineage-helper-owner-checkpoint
  (with-fixture
    (fn [{:keys [prepared configuration admission]}]
      (let [base (resident/adopt-admitted prepared configuration admission)
            loaded (resident/load-source base (hosted-model/request :run))
            active (:context loaded) invoke raw/call
            applications (atom 0) helpers (atom 0) latest (atom nil)
            error (with-redefs [raw/call
                                (fn [session world target args]
                                  (if (= target (:root imports/helpers))
                                    (let [_ (swap! helpers inc)
                                          [world resource] (m/resource world "resident-lineage-error")
                                          [world io] (m/allocate world :ctor 1 [resource])
                                          functions (assoc (:functions world) ["lineage-helper-added-code"]
                                                           {:params [] :body [:return [:imm 0]]})
                                          world (assoc world :functions functions :result io)
                                          session (raw/open-functions functions (:bindings session)
                                                                      (raw/session-options session))]
                                      (reset! latest {:world world :session session :io io})
                                      (throw (ex-info "injected post-application lineage helper failure"
                                                      {:checkpoint world :checkpoint-session session
                                                       :witness-raw-result io :temporary-owners [io]})))
                                    (do (swap! applications inc) (invoke session world target args))))]
                    (failure #(resident/call active (:file loaded) hosted-model/answer-name [nil [1 2]]
                                             {:arguments [:erased :bytes] :result :bytes})))
            packet (ex-data error) checkpoint (:checkpoint packet)
            completed (:resident-completed-invocation packet)
            entry (:resident-lineage-entry packet)
            io (:witness-raw-result packet)]
        (is (some? error))
        (is (= 1 @applications @helpers))
        (is (identical? (:world @latest) checkpoint))
        (is (identical? (:session @latest) (:checkpoint-session packet)))
        (is (identical? (:functions checkpoint) (get-in packet [:checkpoint-session :functions])))
        (is (= (:io @latest) io))
        (is (= [io] (:temporary-owners packet)))
        (is (= 1 (rc checkpoint io)))
        (is (not (contains? packet :resident-owned-result)))
        (is (contains? (get-in completed [:state :heap]) (:id (:value completed))))
        (is (not (contains? (:heap checkpoint) (:id (:value completed)))))
        (is (= (:heap (:world entry)) (:heap (m/release checkpoint io 1))))
        (is (= (rc (:world entry) (:environment entry)) (rc checkpoint (:environment entry))))
        (resident/close! active)
        (resident/close! base)))))

(deftest fork-validates-the-existing-private-environment-snapshot-before-refresh
  (with-fixture
    (fn [{:keys [prepared configuration admission]}]
      (let [context (resident/adopt-admitted prepared configuration admission)
            state (.-state ^prototype.resident_frontend.Context context)
            original @state
            environment (get-in original [:prepared :environment])
            calls (atom 0)]
        (try
          ;; Advanced host-state mutation is an invariant regression model, not
          ;; an untrusted-input or sandbox authority claim.
          (swap! state assoc-in [:prepared :world :heap (:id environment) :fields] [])
          (with-redefs [raw/call (fn [& _] (swap! calls inc) (throw (ex-info "Must not refresh" {})))]
            (is (thrown-with-msg? Exception #"kernel lineage" (resident/fork context))))
          (is (zero? @calls))
          (finally (reset! state original) (resident/close! context)))))))
