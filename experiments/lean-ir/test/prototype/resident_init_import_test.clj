(ns prototype.resident-init-import-test
  "Small verified native Store and genuine fresh Java checking; import/frontend
   helper bodies are explicit models through real raw guest transport."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.resident-init-prefix :as sut]
            [prototype.resident-init-prefix-test :as prefix-model]
            [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.source-import-test :as source-model]
            [prototype.source-module :as export]
            [prototype.module-import :as imports]
            [prototype.module-import-test :as model]
            [prototype.frontend :as frontend]
            [prototype.frontend-test :as frontend-model]
            [prototype.kernel-bridge-test :as guest]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw])
  (:import [ansatz.kernel Env Name]))

(def request {:text "import SourceA\ndef next := 42\n" :file-name "OverInitB.lean"
              :module-name (Name/mkStr Name/ANONYMOUS_NAME "OverInitB")
              :roots [] :initialization :defer})
(def requests (conj source/init-requests (first source-model/requests)))
(def budgets {:outer-fuel 20 :helper-fuel 1000000 :attempt-fuel 10000000})
(def options {:kernel-policy {:allow-axioms? true :allow-unsafe? true} :budgets budgets})
(defn error-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))

(defn with-fixture [backend f & {:keys [header-change assembly-error? finalizer-error? omit-source? throw-finalizer? bad-adoption? world-transform finalizer-hook configure]
                               :or {header-change identity world-transform identity configure identity}}]
  (prefix-model/with-fixture backend
    (fn [{:keys [context checked native-bindings configuration source] :as base}]
      (let [original (resident/snapshot context)
            native-values (vec (vals (get-in checked [:certificate :constants])))
            {:keys [world compiled name root]} (source-model/ordinary-fixture (:world original))
            [world level] (guest/ctor world 1 [guest/nil-tag] 8)
            [world type] (guest/ctor world 3 [level] 8)
            [world body] (guest/ctor world 3 [guest/nil-tag] 8)
            [world answer] (guest/declaration world "answer" type body)
            world (world-transform world)
            compiled (assoc compiled :world world)
            exporter (source-model/ordinary-invoke root)
            export-invoke (fn [world target args]
                            (if (= target export/export-helper)
                              (let [[world io] (exporter world target args)
                                    pair (first (:fields (m/node world io)))
                                    data (first (:fields (m/node world pair)))
                                    constants (nth (:fields (m/node world data)) 2)
                                    old (first (:fields (m/node world constants)))
                                    world (-> world (m/retain answer 1) (m/release old 1)
                                              (m/replace-node constants (assoc (m/node world constants) :fields [answer])))]
                                [world io])
                              (exporter world target args)))
            registered (source/register-compiled-over-init world export-invoke compiled name)
            values (cond-> native-values (not omit-source?) (conj answer))
            checking (source-model/final-invoke values requests 1)
            finalizer-calls (atom 0) assembly-calls (atom 0)
            adoption-root ["str" ["anonymous"] "InitImportAdoptionRoot"]
            dispatch (fn [ctx world target args]
                       (cond
                         (= target adoption-root)
                         (if (= (:environment checked) (first args))
                           (checking world (:root imports/helpers) args) [world 0])
                         (= target source/hybrid-assemble-helper)
                         (do (swap! assembly-calls inc)
                           (if assembly-error?
                             (let [[world message] (m/resource world "assembly-error")]
                               (m/allocate world :ctor 1 [message]))
                             (let [[prefix data _ path] args
                                   [world pair] (source-model/part world data path)
                                   world (m/release world data 1)
                                   region (second (:fields (m/node world pair)))
                                   [world state] (m/allocate world :ctor 0 [prefix pair])
                                   [world imports] (m/allocate world :array 246 [])
                                   [world assembly] (m/allocate (m/retain world region 1) :ctor 0 [state imports region])]
                               (m/allocate world :ctor 0 [assembly]))))
                         (= target (:finalize source/helpers))
                         (let [[state imports] args
                               _ (swap! finalizer-calls inc)
                               world (if finalizer-hook (finalizer-hook ctx world values) world)
                               world (-> world (m/release state 1) (m/release imports 1))]
                           (when throw-finalizer?
                             (let [world (assoc world :fixture-child-checkpoint true)]
                               ((:checkpoint! ctx) world)
                               ((:switch-backend! ctx) world :mutable)
                               (throw (ex-info "Exact child callback failure" {:fixture-child-failure? true}))))
                           (if (if (fn? finalizer-error?) (finalizer-error?) finalizer-error?)
                             (let [[world message] (m/resource world "finalizer-error")]
                               (m/allocate world :ctor 1 [message]))
                             (source-model/final-result world values)))
                         :else (checking world target args)))
            arities (merge (into {} (for [[key target] imports/helpers]
                                      [target ({:part 3 :request 4 :module 9 :state 1 :finalize 3
                                                :root 1 :constant-map 1 :constants 1 :quot-init? 1} key)]))
                           {source/hybrid-assemble-helper 5 (:finalize source/helpers) 4 (:header source/helpers) 1 adoption-root 1})
            signatures (into {} (for [[target arity] arities]
                                 [target {:params (vec (repeat arity {:ty "object" :borrow false}))
                                          :return-type (if (= target (:quot-init? imports/helpers)) "uint8" "object")}]))
            new-bindings (into {} (for [[target signature] signatures]
                                   [(str "init_import_fixture_" (pr-str target))
                                    {:signature signature :handler (fn [ctx world args] (dispatch ctx world target args))}]))
            native (merge native-bindings new-bindings)
            hybrid (merge (:trusted-bindings configuration) new-bindings)
            helpers (into {} (for [[target signature] signatures]
                               (let [params (vec (range 1 (inc (count (:params signature))))) dest (inc (count params))
                                     symbol (str "init_import_fixture_" (pr-str target))]
                                 [target {:params params :raw-extern {:symbol symbol :signature signature}
                                          :body [:host symbol (mapv #(vector :var %) params) dest [:return [:var dest]]]}])))
            header (header-change (assoc (frontend-model/header) :fileName (:file-name request) :requestedImports requests))
            header-function (get-in (frontend-model/setup backend (frontend-model/envelope false) header)
                                    [:world :functions frontend/header-target])
            functions (merge (:functions (:world original)) (:functions (:world registered)) helpers
                             {frontend/header-target header-function})
            world (assoc (:world registered) :functions functions)
            configured (configure {:world world :functions functions :native native :hybrid hybrid})
            world (:world configured) functions (:functions configured)
            native (:native configured) hybrid (:hybrid configured)
            config (cond-> {:trusted-functions functions :trusted-bindings hybrid}
                     bad-adoption? (assoc :kernel-helpers (assoc imports/helpers :root adoption-root)))
            prepared (assoc original :world world :session (raw/open-functions functions hybrid {:backend backend :fuel 1000000}))
            next-context (resident/adopt-prepared prepared config)
            prefix (sut/prepare-init-prefix next-context checked {:configuration config :native-bindings native})]
        (try (f {:context (:context prefix) :prefix (:prefix prefix) :original next-context
                 :checked checked :source source :configuration config :assembly-calls assembly-calls
                 :finalizer-calls finalizer-calls})
             (finally (resident/close! (:context prefix)) (resident/close! next-context)))))))

(defn prepare [f & [opts]]
  (sut/prepare-source-import-over-init (:context f) request (:prefix f) (or opts options)))
(defn run-to-io! [control]
  (loop [n 0]
    (when (> n 1000) (throw (ex-info "Test did not reach IO completion" {})))
    (let [r (sut/advance-import! control {:max-operations 1 :wall-ms 1000})]
      (if (= :io-completed (get-in r [:progress :phase])) r (recur (inc n))))))

(deftest staged-finalization-checks-fresh-whole-map-and-receipts-only-source
  (doseq [backend [:reference :mutable :jvm]]
    (with-fixture backend
      (fn [{:keys [context finalizer-calls checked source] :as f}]
        (let [before (resident/snapshot context) {:keys [control]} (prepare f)]
          (is (zero? @finalizer-calls))
          (is (some? (error-of #(sut/finish-import! control))))
          (is (= :io-completed (get-in (run-to-io! control) [:progress :phase])))
          (is (= 1 @finalizer-calls))
          (let [result (sut/finish-import! control)
                after (resident/snapshot (:context result))
                receipts (vals (get-in after [:world :source-modules source-model/module :imports]))
                receipt (first receipts) ^Env env (:checked-env receipt)]
            (is (= request (:request result)))
            (is (= requests (get-in result [:header :requestedImports])))
            (is (= 1 (get-in result [:import-receipt :constant-count])))
            (is (= #{"answer"} (set (map str (keys (:constants receipt))))))
            (is (= 18 (count (.allConstants env))))
            (is (not (identical? env (get-in checked [:certificate :env]))))
            (doseq [[name ci] (get-in checked [:certificate :projected])]
              (is (identical? ci (.lookup env name))))
            (is (= 1 (count (get-in after [:world :source-import-prefixes]))))
            (is (identical? before (resident/snapshot context)))
            (is (false? @(:closed source)))
            (is (= 1 @finalizer-calls))
            ;; Exhausted controls remain issued and reject with the same public
            ;; phase, without running another helper or changing either branch.
            (doseq [attempt [#(sut/finish-import! control) #(run-to-io! control)]]
              (let [error (error-of attempt)]
                (is (some? error))
                (is (= {:phase :finished} (ex-data error)))))
            (is (= 1 @finalizer-calls))
            (doseq [snapshot [before after]]
              (let [called (raw/call (:session snapshot) (:world snapshot) ["answer"] [])]
                (is (= 42 (:value called)))))
            (is (identical? before (resident/snapshot context)))
            (is (identical? after (resident/snapshot (:context result))))
            (resident/close! (:context result))
            (is (false? @(:closed source)))))))))

(deftest header-policy-and-budget-bypasses-reject-before-assembly
  (doseq [change [#(assoc % :requestedImports [])
                  #(update % :requestedImports (comp vec reverse))
                  #(update % :requestedImports conj (last requests))
                  #(assoc-in % [:requestedImports 2 :isMeta] true)
                  #(assoc-in % [:requestedImports 2 :module] source/init-module)
                  #(assoc % :moduleSystem true)]]
    (with-fixture :reference
      (fn [{:keys [assembly-calls context] :as f}]
        (let [before (resident/snapshot context) error (error-of #(prepare f))]
          (is (some? error)) (is (:resident-init-import-terminal? (ex-data error)))
          (is (zero? @assembly-calls)) (is (identical? before (resident/snapshot context)))))
      :header-change change))
  (with-fixture :reference
    (fn [{:keys [assembly-calls] :as f}]
      (doseq [opts [(assoc-in options [:kernel-policy :projection-certificate] {})
                    (assoc-in options [:kernel-policy :allow-unsafe?] 1)
                    (assoc-in options [:budgets :outer-fuel] 0)
                    (assoc options :configuration {})]]
        (is (some? (error-of #(prepare f opts)))))
      (is (zero? @assembly-calls)))))

(deftest controls-cannot-be-forged-or-resumed-after-observer-or-reservation-failure
  (is (some? (error-of #(sut/advance-import! (prototype.resident_init_prefix.InitImport.) {:max-operations 1 :wall-ms 1}))))
  (with-fixture :reference
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f (assoc-in options [:budgets :attempt-fuel] 1))
            error (error-of #(run-to-io! control))]
        (is (re-find #"cannot reserve" (.getMessage error)))
        (is (zero? @finalizer-calls))
        (is (some? (error-of #(run-to-io! control)))))
      (let [{:keys [control]} (prepare f)
            error (error-of #(sut/advance-import! control {:max-operations 1 :wall-ms 1000
                               :observe! (fn [_] (throw (ex-info "observer failed" {})))}))]
        (is (re-find #"observer failed" (.getMessage error)))
        (is (map? (:resident-init-import-event (ex-data error))))
        (is (:resident-init-import-terminal? (ex-data error)))
        (is (some? (error-of #(run-to-io! control))))))))

(deftest assembly-and-finalizer-io-errors-retain-owned-terminal-packets
  (with-fixture :reference
    (fn [f]
      (let [error (error-of #(prepare f)) data (ex-data error)]
        (is (m/ref? (:io-result data)))
        (is (= :io-error (get-in data [:resident-init-import-assembly :status])))))
    :assembly-error? true)
  (with-fixture :reference
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f) _ (run-to-io! control)
            error (error-of #(sut/finish-import! control)) data (ex-data error)]
        (is (= 1 @finalizer-calls))
        (is (m/ref? (:resident-init-import-io data)))
        (is (= :io-error (get-in data [:resident-init-import-finalization :status])))
        (is (some? (error-of #(sut/finish-import! control))))))
    :finalizer-error? true))

(deftest checked-init-alone-cannot-earn-source-receipt
  (with-fixture :reference
    (fn [f]
      (let [{:keys [control]} (prepare f) _ (run-to-io! control)
            error (error-of #(sut/finish-import! control)) data (ex-data error)]
        (is (re-find #"published import graph" (.getMessage error)))
        (is (:resident-init-import-terminal? data))
        (is (= :ok (get-in data [:source-finalization-result :status])))
        (is (= 17 (count (get-in data [:source-finalization-result :certificate :constants]))))
        (is (some? (error-of #(sut/finish-import! control))))))
    :omit-source? true))

(deftest helper-budget-is-reserved-before-callback-and-observer-cannot-reenter
  (with-fixture :reference
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f (assoc-in options [:budgets :attempt-fuel] 20))
            error (error-of #(run-to-io! control)) data (ex-data error)]
        (is (re-find #"cannot reserve" (.getMessage error)))
        (is (= :boundary (get-in data [:resident-init-import-event :status])))
        (is (zero? @finalizer-calls))
        (is (= 1 (get-in data [:resident-init-import-progress :completed-operations]))))
      (let [{:keys [control]} (prepare f)
            denied (atom [])
            r (sut/advance-import! control
                {:max-operations 100 :wall-ms 1000
                 :observe! (fn [_]
                             (swap! denied conj
                                    (some? (error-of #(sut/advance-import! control {:max-operations 1 :wall-ms 1}))))
                             (swap! denied conj (some? (error-of #(sut/finish-import! control)))))})]
        (is (= :io-completed (get-in r [:progress :phase])))
        (is (seq @denied)) (is (every? true? @denied))
        (is (= 1 @finalizer-calls))
        (resident/close! (:context (sut/finish-import! control)))))))

(deftest private-native-projection-reuse-does-not-bypass-current-kernel-policy
  (with-fixture :reference
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f (assoc options :kernel-policy {:allow-axioms? false :allow-unsafe? false}))
            _ (run-to-io! control)
            error (error-of #(sut/finish-import! control)) data (ex-data error)]
        (is (some? error))
        (is (:resident-init-import-terminal? data))
        (is (= :checking-started (get-in data [:resident-init-import-progress :phase])))
        (is (map? (:finalization-entry data)))
        (is (= :done (get-in data [:resident-init-import-event :status])))
        (is (m/ref? (:resident-init-import-io data)))
        (is (= 1 @finalizer-calls))
        (is (some? (error-of #(sut/finish-import! control))))))))

(deftest closed-lease-and-postcompletion-observer-failure-are-terminal
  (with-fixture :reference
    (fn [{:keys [source finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f)]
        (.close ^java.io.Closeable source)
        (let [error (error-of #(run-to-io! control))]
          (is (some? error)) (is (zero? @finalizer-calls))
          (is (:resident-init-import-terminal? (ex-data error)))))))
  (with-fixture :reference
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f)
            error (error-of #(sut/advance-import! control
                               {:max-operations 100 :wall-ms 1000
                                :observe! (fn [p] (when (= :io-completed (:phase p))
                                                    (throw (ex-info "after completed IO" {}))))}))
            data (ex-data error)]
        (is (re-find #"after completed IO" (.getMessage error)))
        (is (= :done (get-in data [:resident-init-import-event :status])))
        (is (m/ref? (:resident-init-import-io data)))
        (is (identical? (:checkpoint data) (get-in data [:resident-init-import-event :state])))
        (is (= 1 @finalizer-calls))
        (is (some? (error-of #(sut/finish-import! control))))))))

(deftest failed-callback-retains-the-same-wrapper-and-newer-child-world-session
  (with-fixture :jvm
    (fn [{:keys [finalizer-calls] :as f}]
      (let [{:keys [control]} (prepare f)
            error (error-of #(run-to-io! control)) data (ex-data error)]
        (is (:fixture-child-failure? data))
        (is (true? (get-in data [:checkpoint :fixture-child-checkpoint])))
        (is (= :mutable (get-in data [:checkpoint-session :backend])))
        (is (= :boundary (get-in data [:resident-init-import-event :status])))
        (is (not (identical? (:checkpoint data) (get-in data [:resident-init-import-event :state]))))
        (is (= 1 @finalizer-calls))
        (is (identical? error (error-of #(run-to-io! control))))
        (is (identical? error (error-of #(sut/finish-import! control))))))
    :throw-finalizer? true))

(deftest postchecking-adoption-failure-retains-fresh-whole-map-and-owned-packet
  (with-fixture :reference
    (fn [{:keys [context finalizer-calls] :as f}]
      (let [before (resident/snapshot context)
            {:keys [control]} (prepare f) _ (run-to-io! control)
            error (error-of #(sut/finish-import! control)) data (ex-data error)
            finished (:resident-init-import-finalization data)
            prepared (:resident-init-import-adoption-entry data)]
        (is (some? error))
        (is (= :adopt-started (get-in data [:resident-init-import-progress :phase])))
        (is (= :ok (:status finished)))
        (is (= 18 (count (get-in finished [:certificate :constants]))))
        (is (= 1 (count (get-in finished [:source-import-receipt :constants]))))
        (is (= (:environment finished) (:environment prepared)))
        (is (= 1 (count (get-in prepared [:world :source-import-prefixes]))))
        (is (= :released (get-in data [:resident-init-import-ownership :module-name-state])))
        (is (= :released (get-in data [:resident-init-import-ownership :prior-environment-in-new-branch])))
        (is (identical? before (resident/snapshot context)))
        (is (= 1 @finalizer-calls))
        (is (identical? error (error-of #(sut/finish-import! control))))))
    :bad-adoption? true))

(deftest captured-source-is-not-reopened-and-operation-owns-an-independent-branch
  (with-fixture :reference
    (fn [{:keys [context prefix source] :as f}]
      (let [path (java.io.File/createTempFile "resident-init-import-" ".lean" (java.io.File. "target"))
            fork (resident/fork context)]
        (try
          (spit path (:text request))
          (let [{:keys [control]} (sut/prepare-source-import-over-init fork
                                   (-> request (dissoc :text) (assoc :path (.getPath path))) prefix options)
                released (sut/release-prefix context prefix)]
            (spit path "changed after capture")
            (is (some? (error-of #(sut/prepare-source-import-over-init (:context released) request prefix options))))
            (resident/close! fork)
            (run-to-io! control)
            (let [result (sut/finish-import! control)]
              (is (= request (:request result)))
              (is (not (contains? (:request result) :path)))
              (is (= 1 (count (get-in (resident/snapshot (:context result)) [:world :source-import-prefixes]))))
              (is (false? @(:closed source)))
              (resident/close! (:context result)))
            (resident/close! (:context released)))
          (finally (.delete path) (resident/close! fork)))))))
