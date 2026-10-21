(ns prototype.resident-import-test
  "Real guest encoding/raw transport and production source assembly/finalization
   with fresh Java checking of a safe closed identity CI. Parser/finalizer helper
   bodies are explicit models over the native mixed-witness fixture. No full Lean
   frontend/finalizer or whole-environment parity claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.resident-import :as sut]
            [prototype.resident-frontend :as resident]
            [prototype.source-file-typed-witness-test :as typed]
            [prototype.source-import :as source]
            [prototype.source-import-test :as source-model]
            [prototype.module-import :as imports]
            [prototype.module-import-test :as import-model]
            [prototype.frontend :as frontend]
            [prototype.frontend-test :as frontend-model]
            [prototype.hosted-file-test :as hosted]
            [prototype.guest-encoding :as encoding]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as guest]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.runtime-prim :as prim])
  (:import [ansatz.kernel Env Name]))

(def requests [{:module typed/module-a :importAll false :isExported true :isMeta false}])
(def request {:text "prelude\nimport PreludeIdentity\n\ndef second := 42\n"
              :file-name "ResidentImportB.lean" :module-name (Name/mkStr Name/ANONYMOUS_NAME "ResidentImportB")
              :roots [(Name/mkStr Name/ANONYMOUS_NAME "second")] :initialization :defer})

(defn fixture [backend & {:keys [header-change world-change values-change io-error? bad-adoption? illtyped?]
                          :or {header-change identity world-change identity values-change identity}}]
  (let [base (typed/setup backend (fn [w _] w) identity)
        env (:environment base) start (:world base)
        published (get-in start [:source-modules typed/module-a])
        data (:data published) digest (:unit-digest published)
        key (str "ansatz-source:" digest)
        values (get-in base [:finished :certificate :constants])
        ci (get values (Name/mkStr Name/ANONYMOUS_NAME "answer"))
        definition (first (:fields (m/node start ci)))
        constant-val (first (:fields (m/node start definition)))
        type (nth (:fields (m/node start constant-val)) 2)
        [start invalid-ci] (if illtyped? (guest/declaration start "answer" type type) [start nil])
        final-values (if illtyped? [invalid-ci] (values-change [ci]))
        calls (atom [])
        checking (import-model/helper-model calls final-values :io-error? io-error?)
        assembly (source-model/invoke (first (:fields (m/node start env))))
        final-header (json/write-str {:schema "lean-source-import-header/1"
                                     :producer "SourceModuleImport.finalizerHeader"
                                     :leanCommit (get prim/pinned-build "lean_get_githash")
                                     :moduleSystem false :imports requests})
        signatures {(:assemble source/helpers) {:params [{:ty "object" :borrow false}
                                                         {:ty "object" :borrow true}
                                                         {:ty "object" :borrow true}] :return-type "object"}
                    (:finalize source/helpers) {:params [{:ty "object" :borrow false}
                                                         {:ty "object" :borrow false}
                                                         {:ty "object" :borrow true}
                                                         {:ty "void" :borrow false}] :return-type "object"}
                    (:header source/helpers) {:params [{:ty "object" :borrow true}] :return-type "object"}}
        signatures (merge signatures
                          (into {} (map (fn [key] [(get imports/helpers key)
                                                  {:params [{:ty "object" :borrow true}]
                                                   :return-type (if (= key :quot-init?) "uint8" "object")}])
                                        [:root :constants :constant-map :quot-init?])))
        bindings (into {} (for [[target signature] signatures]
                            (let [symbol (str "resident_import_fixture_" (pr-str target))]
                              [symbol {:signature signature
                                       :handler (fn [_ world args]
                                                  (cond
                                                    (= target (:assemble source/helpers)) (assembly world target args)
                                                    (= target (:finalize source/helpers)) (checking world (:finalize imports/helpers) args)
                                                    (= target (:header source/helpers)) [world final-header]
                                                    :else (checking world target args)))}])))
        helpers (into {} (for [[target signature] signatures]
                           (let [params (vec (range 1 (inc (count (:params signature)))))
                                 symbol (str "resident_import_fixture_" (pr-str target))
                                 dest (inc (count params))]
                             [target {:params params :raw-extern {:symbol symbol :signature signature}
                                      :body [:host symbol (mapv #(vector :var %) params) dest [:return [:var dest]]]}])))
        header (header-change (assoc (frontend-model/header) :fileName (:file-name request) :requestedImports requests))
        parser (frontend-model/setup backend (frontend-model/envelope false) header)
        alternate-root ["str" ["anonymous"] "invalidImportAdoptionRoot"]
        functions (merge (:functions start) @hosted/encoders helpers (:functions (:world parser))
                         {alternate-root {:params [1] :body [:return [:imm 0]]}})
        world (-> start (assoc :functions functions) (m/retain env 1)
                  (assoc-in [:source-modules typed/module-a] (assoc published :key key :environment env))
                  (assoc-in [:source-regions key] {:module typed/module-a :data data :anchors {}})
                  world-change)
        configuration {:trusted-functions functions :trusted-bindings bindings}
        prepared {:world world :session (raw/open-functions (:functions world) bindings {:backend backend :fuel 1000000})
                  :environment env :options 0 :catalogue (get-in base [:options :catalogue])}
        ; Options must be an owned reference for the resident API.
        [world options] (m/allocate world :ctor 0 [])
        prepared (assoc prepared :world world :options options
                         :certificate {:stale true} :associated-env :stale
                         :fresh-verification-certificate {:stale true}
                         :source-import-receipt {:stale true})
        context (resident/adopt-prepared prepared configuration)
        _ (reset! calls [])]
    {:context context :configuration (cond-> configuration
                                      bad-adoption? (assoc :kernel-helpers
                                                       (assoc imports/helpers :root alternate-root))) :calls calls :base base :digest digest :ci ci}))

(defn prepare [fixture]
  (sut/prepare-source-import (:context fixture) request
    {:profile :standalone :configuration (:configuration fixture) :kernel-policy {}}))
(defn error-of [f] (try (f) nil (catch clojure.lang.ExceptionInfo error error)))

(deftest preparation-creates-fresh-checked-receipt-without-changing-input
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [context digest base] :as f} (fixture backend)
          before (resident/snapshot context)
          result (prepare f) after (resident/snapshot (:context result))
          receipts (get-in after [:world :source-modules typed/module-a :imports])
          envs (set (map :checked-env (vals receipts)))
          original-env (get-in base [:finished :certificate :env])]
      (is (= request (:request result)))
      (is (= requests (get-in result [:header :requestedImports])))
      (is (= {:module typed/module-a :unit-digest digest :constant-count 1} (:import-receipt result)))
      (is (= 2 (count envs))) ; independent old and freshly checked import receipts
      (is (some #(not (identical? original-env %)) envs))
      (doseq [^Env env envs]
        (is (some? (.lookup env (Name/mkStr Name/ANONYMOUS_NAME "answer")))))
      (is (not= (:environment before) (:environment after)))
      (is (not-any? #(contains? after %) [:certificate :associated-env
                                        :fresh-verification-certificate :source-import-receipt]))
      (is (= 1 (:rc (m/node (:world after) (:environment after)))))
      (is (identical? before (resident/snapshot context)))
      (is (identical? (:source-modules (:world before))
                      (:source-modules (:world (resident/snapshot context)))))
      (resident/close! (:context result)) (resident/close! context))))

(deftest text-is-captured-once-for-later-compilation
  (let [f (fixture :reference)
        path (java.io.File/createTempFile "resident-import-capture-" ".lean" (io/file "target"))]
    (try
      (spit path (:text request))
      (let [result (sut/prepare-source-import (:context f)
                     (-> request (dissoc :text) (assoc :path (.getPath path)))
                     {:profile :standalone :configuration (:configuration f) :kernel-policy {}})]
        (spit path "changed after preparation")
        (is (= (:text request) (get-in result [:request :text])))
        (is (not (contains? (:request result) :path)))
        (is (= (:file-name request) (get-in result [:request :file-name])))
        (resident/close! (:context result)))
      (finally (io/delete-file path true) (resident/close! (:context f))))))

(deftest unsupported-profiles-and-checking-bypasses-fail-before-guest-execution
  (let [{:keys [context configuration calls]} (fixture :reference)
        before (resident/snapshot context)]
    (doseq [options [{:profile :over-init :configuration configuration :kernel-policy {}}
                     {:profile :standalone :configuration configuration}
                     {:profile :standalone :configuration configuration :kernel-policy {:projection-certificate {}}}
                     {:profile :standalone :configuration configuration :kernel-policy {:allow-axioms? 1}}
                     {:profile :standalone :configuration configuration :kernel-policy {:fuel 0}}
                     {:profile :standalone :configuration configuration :kernel-policy {} :resolver identity}]]
      (let [error (error-of #(sut/prepare-source-import context request options))]
        (is (some? error)) (is (:resident-import-terminal? (ex-data error)))
        (is (nil? (:resident-import-header (ex-data error))))
        (is (identical? (:world before) (:checkpoint (ex-data error))))))
    (is (identical? before (resident/snapshot context)))
    (is (empty? @calls))
    (resident/close! context)))

(deftest only-one-exact-classic-source-import-is-supported
  (doseq [change [#(assoc % :requestedImports [])
                  #(assoc % :requestedImports (conj requests (first requests)))
                  #(assoc % :requestedImports (assoc-in requests [0 :isMeta] true))
                  #(assoc % :requestedImports (assoc-in requests [0 :importAll] true))
                  #(assoc % :moduleSystem true)]]
    (let [{:keys [context] :as f} (fixture :reference :header-change change)
          before (resident/snapshot context) error (error-of #(prepare f))]
      (is (re-find #"classic header" (.getMessage error)))
      (is (= :header-started (:resident-import-phase (ex-data error))))
      (is (nil? (:resident-import-assembly (ex-data error))))
      (is (identical? before (resident/snapshot context)))
      (resident/close! context))))

(deftest numeric-looking-module-segment-remains-a-string-name
  (let [module ["str" ["str" ["anonymous"] "Outer"] "123"]
        f (fixture :reference :header-change #(assoc-in % [:requestedImports 0 :module] module))
        error (error-of #(prepare f)) data (ex-data error)
        encoded (get-in data [:resident-import-ownership :module-name])
        ^Name projected (bridge/project-name (:checkpoint data) encoded)]
    (is (re-find #"not registered" (.getMessage error)))
    (is (.isStr projected)) (is (= "123" (.str projected)))
    (is (= "Outer" (str (.prefix projected))))
    (resident/close! (:context f))))

(deftest exact-unit-and-executable-identity-and-independent-closures-remain-required
  (doseq [change [(fn [world] (update-in world [:eval-const-authorizations :units
                                              (:unit-digest (get-in world [:source-modules typed/module-a]))]
                                        #(with-meta % {:foreign true})))
                  #(update-in % [:functions typed/imported-name] (fn [function] (with-meta function {:foreign true})))]]
    (let [f (fixture :reference :world-change change)
          before (resident/snapshot (:context f)) error (error-of #(prepare f))]
      (is (re-find #"not registered|executable identity changed" (.getMessage error)))
      (is (nil? (:resident-import-assembly (ex-data error))))
      (is (identical? before (resident/snapshot (:context f))))
      (resident/close! (:context f))))
  (let [{:keys [context configuration]} (fixture :reference)
        error (error-of #(sut/prepare-source-import context request
                          {:profile :standalone :configuration
                           (update configuration :trusted-functions dissoc (:finalize source/helpers))
                           :kernel-policy {}}))]
    (is (re-find #"authorized program" (.getMessage error)))
    (is (nil? (:resident-import-header (ex-data error))))
    (resident/close! context)))

(deftest finalizer-errors-and-receipt-rejection-preserve-owned-checkpoints
  (doseq [[options expected] [[[:io-error? true] #"finalizer failed"]
                              [[:values-change (constantly [])] #"Finalized source CI references differ"]]]
    (let [f (apply fixture :reference options)
          before (resident/snapshot (:context f)) error (error-of #(prepare f)) data (ex-data error)]
      (is (re-find expected (.getMessage error)))
      (is (= :finalize-started (:resident-import-phase data)))
      (is (map? (:resident-import-assembly data)))
      (is (= :owned (get-in data [:resident-import-ownership :module-name-state])))
      (is (map? (:checkpoint-session data)))
      (is (identical? before (resident/snapshot (:context f))))
      (when-let [io (:io-result data)] (is (= 1 (:rc (m/node (:checkpoint data) io)))))
      (resident/close! (:context f)))))

(deftest actual-type-checking-rejects-an-illtyped-identity-with-owned-finalization-evidence
  (let [{:keys [context configuration]} (fixture :reference :illtyped? true)
        before (resident/snapshot context)
        error (error-of #(sut/prepare-source-import context request
                          {:profile :standalone :configuration configuration :kernel-policy {}}))
        data (ex-data error)]
    (is (some? error))
    (is (re-find #"kernel association failed" (.getMessage error)))
    (is (= :finalize-started (:resident-import-phase data)))
    (is (map? (:finalization-entry data)))
    (is (m/ref? (get-in data [:finalization-entry :environment])))
    (is (nil? (:resident-import-finalization data)))
    (is (= :owned (get-in data [:resident-import-ownership :module-name-state])))
    (is (identical? before (resident/snapshot context)))
    (resident/close! context)))

(deftest postfinalization-adoption-failure-retains-fresh-packet-and-owners
  (let [f (fixture :reference :bad-adoption? true)
        before (resident/snapshot (:context f))
        error (error-of #(prepare f)) data (ex-data error)
        finished (:resident-import-finalization data)
        world (:checkpoint data)]
    (is (some? error))
    (is (= :adopt-started (:resident-import-phase data)))
    (is (= :ok (:status finished)))
    (is (= 1 (count (get-in finished [:source-import-receipt :constants]))))
    (is (map? (:resident-adoption-entry data)))
    (is (not-any? #(contains? (:resident-adoption-entry data) %)
                  [:certificate :associated-env :fresh-verification-certificate :source-import-receipt]))
    (is (= :released (get-in data [:resident-import-ownership :module-name-state])))
    (is (= :released (get-in data [:resident-import-ownership :prior-environment-in-new-branch])))
    (is (= 1 (:rc (m/node world (:environment finished)))))
    (is (identical? before (resident/snapshot (:context f))))
    (resident/close! (:context f))))
