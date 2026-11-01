(ns prototype.resident-init-prefix-test
  "Small verified native Store, real Java checking and raw guest transport with
   explicitly modelled import-helper bodies. This is not full Init acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-init-prefix :as sut]
            [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.source-import-test :as source-model]
            [prototype.module-import :as imports]
            [prototype.module-import-test :as model]
            [prototype.import-capabilities :as caps]
            [prototype.module-init-capabilities :as init]
            [prototype.frontend-test :as frontend-model]
            [prototype.hosted-file-test :as hosted]
            [prototype.import-ir :as ir]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m])
  (:import [ansatz.kernel Env]))

(defn with-fixture [backend f]
  (source-model/with-tiny-init
    (fn [loaded]
      (let [calls (atom []) root-calls (atom 0) fail-root-at (atom nil) delegate (model/helper-model calls (model/constants loaded))
            checked (imports/import-loaded loaded delegate {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})
            arities {:part 3 :request 4 :module 9 :state 1 :finalize 3 :root 1 :constant-map 1 :constants 1 :quot-init? 1}
            signatures (into {} (for [[key target] imports/helpers]
                                  [target {:params (vec (repeat (arities key) {:ty "object" :borrow false}))
                                           :return-type (if (= key :quot-init?) "uint8" "object")}]))
            bindings (into {} (for [[target signature] signatures]
                               [(str "prefix_fixture_" (pr-str target))
                                {:signature signature :handler (fn [_ w args]
                                  (when (and (= target (:root imports/helpers))
                                             (= (swap! root-calls inc) @fail-root-at))
                                    (throw (ex-info "Selected fixture root failure" {:fixture-failure? true})))
                                  (delegate w target args))}]))
            native (merge bindings (into {} (for [[symbol signature] (assoc caps/signatures "lean_run_mod_init_core" init/signature)]
                                              [symbol {:signature signature :handler (fn [& _] (throw (ex-info "Unused native fixture handler" {})))}])))
            hybrid (source/make-hybrid-bindings native)
            helpers (into {} (for [[target signature] signatures]
                               (let [params (vec (range 1 (inc (count (:params signature))))) dest (inc (count params))
                                     symbol (str "prefix_fixture_" (pr-str target))]
                                 [target {:params params :raw-extern {:symbol symbol :signature signature}
                                          :body [:host symbol (mapv #(vector :var %) params) dest [:return [:var dest]]]}])))
            unused (into {} (for [target (concat (vals source/helpers) [source/hybrid-assemble-helper])]
                             [target {:params [] :body [:return [:imm 0]]}]))
            frontend (:functions (:world (frontend-model/setup backend (frontend-model/envelope false) (frontend-model/header))))
            functions (merge @hosted/encoders frontend helpers unused)
            world (assoc (:world checked) :functions functions)
            [world options] (m/allocate world :ctor 0 [])
            config {:trusted-functions functions :trusted-bindings hybrid}
            prepared {:world world :environment (:environment checked) :options options
                      :catalogue (ir/index-bundles ["fixtures/hosted/PreludeIdentity.ir.jsonl"])
                      :session (raw/open-functions functions hybrid {:backend backend :fuel 1000000})}
            context (resident/adopt-prepared prepared config)]
        (reset! calls []) (reset! root-calls 0)
        (try (f {:context context :checked checked :configuration config :native-bindings native
                 :calls calls :fail-root-at fail-root-at :source (:source loaded)})
             (finally (resident/close! context)))))))

(defn prepare [{:keys [context checked configuration native-bindings]}]
  (sut/prepare-init-prefix context checked {:configuration configuration :native-bindings native-bindings}))
(defn error-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))

(deftest preparation-release-and-forks-have-independent-registry-owners
  (doseq [backend [:reference :mutable :jvm]]
    (with-fixture backend
      (fn [{:keys [context source] :as fixture}]
        (let [before (resident/snapshot context) result (prepare fixture)
              prepared (:context result) prefix (:prefix result) snapshot (resident/snapshot prepared)
              fork (resident/fork prepared) released (sut/release-prefix prepared prefix)
              again (sut/release-prefix fork prefix)
              raw-prefix (first (vals (get-in snapshot [:world :source-import-prefixes])))
              state (:state raw-prefix)]
          (is (= source/init-requests (:producer-imports (sut/descriptor prefix))))
          (is (= 17 (:constant-count (sut/descriptor prefix))))
          (is (= 1 (:rc (m/node (:world snapshot) state))))
          (is (= 1 (count (get-in (resident/snapshot fork) [:world :source-import-prefixes]))))
          (is (empty? (get-in (resident/snapshot (:context released)) [:world :source-import-prefixes])))
          (is (not (contains? (:heap (:world (resident/snapshot (:context released)))) (:id state))))
          (is (identical? before (resident/snapshot context)))
          (is (identical? snapshot (resident/snapshot prepared)))
          (is (false? @(:closed source)))
          (is (some? (error-of #(sut/release-prefix (:context released) prefix))))
          (is (some? (error-of #(sut/release-prefix context prefix))))
          (doseq [ctx [(:context released) (:context again) fork prepared]] (resident/close! ctx))
          (is (false? @(:closed source))))))))

(deftest issued-objects-and-explicit-original-checking-result-are-required
  (is (thrown? Exception (sut/descriptor (prototype.resident_init_prefix.InitPrefix.))))
  (is (thrown? Exception (sut/descriptor {})))
  (with-fixture :reference
    (fn [{:keys [context checked configuration native-bindings calls] :as fixture}]
      (let [before (resident/snapshot context)]
        (doseq [candidate [(assoc checked :status :failed)
                           (assoc checked :environment (m/->Ref 999999))
                           (assoc-in checked [:certificate :env] (Env.))
                           (assoc-in checked [:certificate :projection-sources] [])
                           (update-in checked [:certificate :projected]
                                      #(assoc % (first (keys %)) nil))]]
          (let [error (error-of #(prepare (assoc fixture :checked candidate)))]
            (is (some? error))
            (is (:resident-init-prefix-terminal? (ex-data error)))
            (is (= :entry (:resident-init-prefix-phase (ex-data error))))))
        (doseq [options [{:configuration configuration}
                        {:configuration configuration :native-bindings native-bindings :projection-certificate {}}
                        {:configuration (update configuration :trusted-functions dissoc source/hybrid-assemble-helper)
                         :native-bindings native-bindings}
                        {:configuration configuration
                         :native-bindings (assoc native-bindings "lean_run_mod_init_core"
                                                 (assoc (get native-bindings "lean_run_mod_init_core") :handler (fn [& _] nil)))}]]
          (is (some? (error-of #(sut/prepare-init-prefix context checked options)))))
        (is (empty? @calls))
        (is (identical? before (resident/snapshot context)))))))

(deftest altered-branch-scaffold-and-anchor-reject-release-with-exact-terminal-packet
  (with-fixture :reference
    (fn [{:keys [configuration] :as fixture}]
      (let [{:keys [context prefix]} (prepare fixture)
            before (resident/snapshot context)
            raw-prefix (first (vals (get-in before [:world :source-import-prefixes])))
            state-id (:id (:state raw-prefix))
            child (first (remove #{state-id} (keys (:local-nodes raw-prefix))))]
        (doseq [change [(fn [w] (update w :source-import-prefixes dissoc state-id))
                       (fn [w] (assoc-in w [:heap child :changed] true))
                       (fn [w] (assoc-in w [:heap (:base (:source fixture))] {:kind :array :fields [] :rc 1}))]]
          (let [packet (update before :world change)
                candidate (resident/adopt-prepared packet configuration)
                entry (resident/snapshot candidate)
                error (error-of #(sut/release-prefix candidate prefix))]
            (is (some? error))
            (is (:resident-init-prefix-terminal? (ex-data error)))
            (is (identical? (:world entry) (:checkpoint (ex-data error))))
            (is (identical? entry (resident/snapshot candidate)))
            (resident/close! candidate)))
        (resident/close! context)))))

(deftest adoption-failure-preserves-the-prepared-registry-and-current-helper-checkpoint
  (with-fixture :reference
    (fn [{:keys [context fail-root-at] :as fixture}]
      (let [before (resident/snapshot context)]
        ;; The first root call authenticates preparation; the second is the real
        ;; resident adoption helper after successful prefix assembly.
        (reset! fail-root-at 2)
        (let [error (error-of #(prepare fixture)) data (ex-data error)
              prepared (:resident-init-prefix-preparation data)]
          (is (some? error))
          (is (:fixture-failure? data))
          (is (= :adopt-started (:resident-init-prefix-phase data)))
          (is (= 1 (count (get-in prepared [:world :source-import-prefixes]))))
          (is (identical? (:world prepared) (get-in data [:resident-adoption-entry :world])))
          (is (map? (:checkpoint-session data)))
          (is (not (identical? (:world before) (:checkpoint data))))
          (is (= :inherited-in-independent-branch (:resident-init-prefix-root-ownership data)))
          (is (identical? before (resident/snapshot context))))))))

(deftest closed-native-source-is-rejected-on-release-without-mutating-context
  (with-fixture :reference
    (fn [{:keys [source] :as fixture}]
      (let [{:keys [context prefix]} (prepare fixture)
            before (resident/snapshot context)]
        (.close ^java.io.Closeable source)
        (let [error (error-of #(sut/release-prefix context prefix))]
          (is (some? error))
          (is (re-find #"not authenticated" (.getMessage error)))
          (is (identical? (:world before) (:checkpoint (ex-data error))))
          (is (identical? before (resident/snapshot context))))
        (resident/close! context)))))

(deftest release-adoption-failure-retains-the-released-packet-without-consuming-input
  (with-fixture :reference
    (fn [{:keys [fail-root-at] :as fixture}]
      (let [{:keys [context prefix]} (prepare fixture)
            before (resident/snapshot context)]
        ;; Preparation and its adoption consumed two root calls. Release itself
        ;; runs no guest call; this failure is in subsequent Context adoption.
        (reset! fail-root-at 3)
        (let [error (error-of #(sut/release-prefix context prefix)) data (ex-data error)
              released (:resident-init-prefix-released data)]
          (is (:fixture-failure? data))
          (is (= :adopt-started (:resident-init-prefix-phase data)))
          (is (empty? (get-in released [:world :source-import-prefixes])))
          (is (identical? (:world released) (get-in data [:resident-adoption-entry :world])))
          (is (map? (:checkpoint-session data)))
          (is (identical? before (resident/snapshot context)))
          (is (= 1 (count (get-in before [:world :source-import-prefixes])))))
        (resident/close! context)))))
