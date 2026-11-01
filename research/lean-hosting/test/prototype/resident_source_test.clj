(ns prototype.resident-source-test
  "Public facade integration over captured Lean identity IR, real guest Name
   encoding, raw transport and production registration. Frontend/export callbacks
   and starting checked Env are explicit models; no full frontend claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [prototype.resident-source :as sut]
            [prototype.resident-frontend :as resident]
            [prototype.hosted-file-test :as hosted]
            [prototype.frontend-test :as frontend-model]
            [prototype.frontend :as frontend]
            [prototype.source-module :as export]
            [prototype.source-module-test :as export-model]
            [prototype.source-import :as source]
            [prototype.machine :as m]
            [prototype.module-import :as imports]
            [prototype.raw-interop :as raw]
            [prototype.import-ir :as ir])
  (:import [ansatz.kernel Env]))

(def export-symbol "resident_source_export_fixture")
(def identity-code {:params [1] :body [:inc [:var 1] 1 [:return [:var 1]]]})
(def export-signature {:params [{:ty "object" :borrow false}
                                {:ty "object" :borrow false}
                                {:ty "void" :borrow false}] :return-type "object"})

(defn setup [backend profile success & {:keys [io-error? bundle-change export-change distinct-environment? bad-adoption?]
                                      :or {bundle-change identity export-change identity}}]
  (let [requests (if (= profile :over-init) source/init-requests [])
        rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines @hosted/captured))
        rows (-> rows
                 (assoc-in [0 :initializationPlan :imports]
                           (mapv (fn [i] {:module (:module i) :meta (:isMeta i)}) requests))
                 bundle-change)
        bundle (str/join "\n" (map json/write-str rows))
        envelope (assoc (frontend-model/envelope success) :fileName hosted/file-path
                        :mainModule ["str" ["anonymous"] "PreludeIdentity"]
                        :requestedImports requests :bundle (when success bundle))
        header (assoc (frontend-model/header) :fileName hosted/file-path :requestedImports requests)
        base (frontend-model/setup backend envelope header)
        env (get-in base [:arguments :environment])
        calls (atom [])
        delegate (export-model/invoke-model calls
                   #(assoc % :module ["str" ["anonymous"] "PreludeIdentity"] :imports requests)
                   :io-error? io-error?)
        handler (fn [_ world args]
                  (let [[world value] (delegate world export/export-helper args)
                        world (export-change world)]
                    (if (or io-error? (= profile :over-init)) [world value]
                      (let [pair (first (:fields (m/node world value)))
                            data (first (:fields (m/node world pair)))
                            array (first (:fields (m/node world data)))
                            old (:fields (m/node world array))
                            world (m/replace-node world array (assoc (m/node world array) :fields []))]
                        [(reduce #(m/release %1 %2 1) world old) value]))))
        bindings {export-symbol {:signature export-signature :handler handler}}
        [initial-world root] (if distinct-environment?
                               (m/allocate (:world base) :ctor 0 [])
                               [(:world base) env])
        initial-world (if distinct-environment?
                        (-> initial-world
                            (m/replace-node env (assoc (m/node initial-world env) :fields [root]))
                            (m/retain root 1))
                        (m/retain initial-world env 1))
        getter (if distinct-environment?
                 {:params [1] :body [:let 2 [:project [:var 1] 0]
                                     [:inc [:var 2] 1 [:return [:var 2]]]]}
                 identity-code)
        compiler (get-in base [:world :functions frontend/compile-target])
        compiler (if distinct-environment?
                   (assoc compiler :body
                     [:let 10 [:project [:var 1] 0]
                      [:inc [:var 10] 1 [:dec [:var 1] 1
                        [:let 11 [:ctor 0 [[:var 10]]]
                         (walk/postwalk #(if (= [:var 1] %) [:var 11] %) (:body compiler))]]]])
                   compiler)
        alternate-root ["str" ["anonymous"] "invalidAdoptionRoot"]
        functions (merge @hosted/encoders (:functions (:world base))
                         (zipmap (vals export/ir-export-targets) (repeat identity-code))
                         {(:root imports/helpers) getter
                          (:constant-map imports/helpers) getter
                          alternate-root {:params [1] :body [:return [:imm 0]]}
                          frontend/compile-target compiler
                          (:quot-init? imports/helpers) {:params [1] :body [:return [:imm 0]]}
                          export/export-helper
                          {:params [1 2 3] :raw-extern {:symbol export-symbol :signature export-signature}
                           :body [:host export-symbol [[:var 1] [:var 2] [:var 3]] 4 [:return [:var 4]]]}})
        world (-> initial-world (assoc :functions functions)
                  (assoc-in [:kernel-environments (:id root)]
                    {:anchor root :env (Env.) :constant-map root :quot-init? false}))
        prepared {:world world :session (raw/open-functions functions bindings {:backend backend :fuel 1000000})
                  :environment env :options (get-in base [:arguments :options])
                  :catalogue (ir/index-bundles ["fixtures/hosted/PreludeIdentity.ir.jsonl"])}
        configuration {:trusted-functions functions :trusted-bindings bindings}
        context (resident/adopt-prepared prepared configuration)]
    {:context context :configuration (cond-> configuration
                                      bad-adoption? (assoc :kernel-helpers
                                                       (assoc imports/helpers :root alternate-root)))
     :profile profile :calls calls
     :request (hosted/request :defer)}))

(defn publish [{:keys [context configuration profile request]}]
  (sut/load-and-publish context request {:profile profile :configuration configuration}))
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo error error)))

(deftest publication-preserves-old-context-and-inherited-fork
  (doseq [backend [:reference :mutable :jvm] profile [:standalone :over-init]]
    (let [{:keys [context calls] :as fixture} (setup backend profile true)
          before (resident/snapshot context)
          result (publish fixture)
          active (:context result) p (resident/snapshot active)
          fork (resident/fork active)
          called (resident/call fork (:file result) hosted/answer-name [nil 42]
                               {:arguments [:erased :nat] :result :nat})
          module ["str" ["anonymous"] "PreludeIdentity"]
          entry (get-in p [:world :source-modules module])]
      (is (:success result))
      (is (= profile (get-in result [:publication :profile])))
      (is (= 1 (count @calls)))
      (is (identical? before (resident/snapshot context)))
      (is (nil? (get-in before [:world :source-modules])))
      (is (identical? (:unit entry)
                     (get-in p [:world :eval-const-authorizations :units (:unit-digest entry)])))
      (is (= 3 (:rc (m/node (:world p) (:environment p))))) ; association + context + registry
      (is (= 42 (:value called)))
      (resident/close! active)
      (let [called-again (resident/call fork (:file result) hosted/answer-name [nil 43]
                                        {:arguments [:erased :nat] :result :nat})]
        (is (= 43 (:value called-again)))
        (resident/close! (:context called-again)))
      (doseq [ctx [context fork (:context called)]] (resident/close! ctx)))))

(deftest diagnostics-do-not-publish-or-export
  (let [{:keys [context calls] :as fixture} (setup :reference :standalone false)
        before (resident/snapshot context) result (publish fixture)]
    (is (false? (:success result)))
    (is (seq (:diagnostics result)))
    (is (nil? (:file result)))
    (is (nil? (:publication result)))
    (is (empty? @calls))
    (is (nil? (:source-modules (:world (resident/snapshot (:context result))))))
    (is (identical? before (resident/snapshot context)))
    (resident/close! (:context result)) (resident/close! context)))

(deftest explicit-authority-and-selected-closures-are-required
  (let [{:keys [context configuration request calls]} (setup :reference :standalone true)
        before (resident/snapshot context)]
    (doseq [bad [{} {:profile :guess :configuration configuration}
                 {:profile :standalone :configuration (update configuration :trusted-functions dissoc export/export-helper)}
                 {:profile :standalone :configuration
                  (assoc-in configuration [:trusted-functions (first (vals export/ir-export-targets))]
                            (with-meta identity-code {:foreign true}))}
                 {:profile :standalone :configuration (assoc configuration :trusted-bindings {})}]]
      (let [error (failure #(sut/load-and-publish context request bad))]
        (is (some? error))
        (is (:resident-source-terminal? (ex-data error)))
        (is (nil? (:resident-source-compiled (ex-data error))))))
    (is (empty? @calls))
    (is (identical? before (resident/snapshot context)))
    (resident/close! context)))

(deftest registration-failure-preserves-owned-export-and-compilation
  (let [{:keys [context calls] :as fixture} (setup :reference :standalone true :io-error? true)
        before (resident/snapshot context)
        error (failure #(publish fixture)) data (ex-data error)
        world (:checkpoint data) compiled (:resident-source-compiled data)
        owners (:resident-source-ownership data)]
    (is (re-find #"Source module export failed" (.getMessage error)))
    (is (= :register-started (:resident-source-phase data)))
    (is (:success compiled))
    (is (m/ref? (:io-result data)))
    (is (= 1 (:rc (m/node world (:io-result data)))))
    (is (= :owned (:module-name-state owners)))
    (is (= 1 (:rc (m/node world (:module-name owners)))))
    (is (nil? (:resident-source-registration data)))
    (is (= 1 (count @calls)))
    (is (identical? before (resident/snapshot context)))
    (resident/close! context)))

(deftest wrong-import-profiles-and-actions-remain-hard-errors
  (doseq [[actual requested] [[:standalone :over-init] [:over-init :standalone]]]
    (let [{:keys [context calls] :as fixture} (setup :reference actual true)
          error (failure #(publish (assoc fixture :profile requested)))]
      (is (re-find #"same authenticated successful compilation world" (.getMessage error)))
      (is (empty? @calls))
      (is (:success (:resident-source-compiled (ex-data error))))
      (resident/close! context)))
  (let [{:keys [context calls] :as fixture}
        (setup :reference :standalone true :bundle-change
               #(assoc-in % [0 :initializationPlan :actions]
                          [{:meta false :action {:kind "io-unit" :name frontend-model/answer :target frontend-model/answer}}]))
        error (failure #(publish fixture))]
    (is (some? error))
    (is (empty? @calls))
    (resident/close! context)))

(deftest initialization-cannot-run-before-publication-rejection
  (let [{:keys [context request configuration calls]} (setup :reference :standalone true)
        before (resident/snapshot context)
        error (failure #(sut/load-and-publish context (assoc request :initialization :run)
                           {:profile :standalone :configuration configuration}))]
    (is (re-find #"requires deferred initialization" (.getMessage error)))
    (is (nil? (:resident-source-compiled (ex-data error))))
    (is (identical? (:world before) (:checkpoint (ex-data error))))
    (is (empty? @calls))
    (resident/close! context)))

(deftest fixed-registration-helpers-are-protected-with-custom-resident-helpers
  (let [{:keys [context request configuration]} (setup :reference :standalone true)
        prepared (resident/snapshot context)
        alternates (into {} (for [[key value] imports/helpers]
                             [key ["str" ["anonymous"] (str "alternate-" (name key))]]))
        functions (merge (get-in prepared [:world :functions])
                         (zipmap (vals alternates) (repeat identity-code)))
        bindings (get-in prepared [:session :bindings])
        custom (-> configuration (assoc :kernel-helpers alternates)
                   (assoc :trusted-functions functions))
        candidate (-> prepared (assoc-in [:world :functions] functions)
                      (assoc :session (raw/open-functions functions bindings {:backend :reference})))
        ; Host-only readiness intentionally does not acquire/validate associations.
        absent-fixed (update-in custom [:trusted-functions] dissoc (:root imports/helpers))]
    (is (map? (sut/publication-readiness! candidate custom)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"trusted|Trusted|authorized|registry"
          (sut/publication-readiness! candidate absent-fixed)))
    (resident/close! context)))

(deftest post-export-failures-retain-latest-packet-and-exact-authority-checks
  (doseq [[change message]
          [[(fn [world]
              (let [digest (first (keys (get-in world [:eval-const-authorizations :units])))]
                (assoc-in world [:source-regions (str "ansatz-source:" digest)] {:occupied true})))
            #"Conflicting source region key"]
           [(fn [world]
              (let [digest (first (keys (get-in world [:eval-const-authorizations :units])))]
                (update-in world [:eval-const-authorizations :units digest]
                           #(with-meta % {:foreign-unit true}))))
            #"same authenticated successful compilation world"]
           [(fn [world] (update-in world [:functions frontend-model/answer]
                                   #(with-meta % {:foreign-executable true})))
            #"executable identity changed"]]]
    (let [{:keys [context calls] :as fixture}
          (setup :reference :standalone true :export-change change)
          before (resident/snapshot context)
          error (failure #(publish fixture)) data (ex-data error)
          last-call (:resident-source-last-call data)
          returned (get-in last-call [:returned :value])
          returned-world (get-in last-call [:returned :state])
          io-pair (first (:fields (m/node returned-world returned)))
          exported-data (first (:fields (m/node returned-world io-pair)))
          world (:checkpoint data)]
      (is (re-find message (.getMessage error)))
      (is (= 1 (count @calls)))
      (is (= :register-started (:resident-source-phase data)))
      (is (:success (:resident-source-compiled data)))
      (is (= export/export-helper (:target last-call)))
      (is (= 1 (:rc (m/node world exported-data))))
      (is (= :owned (get-in data [:resident-source-ownership :module-name-state])))
      (is (nil? (:resident-source-registration data)))
      (is (identical? before (resident/snapshot context)))
      (resident/close! context))))

(deftest distinct-environment-releases-only-new-branch-prior-owner
  (let [{:keys [context] :as fixture}
        (setup :reference :standalone true :distinct-environment? true)
        before (resident/snapshot context) old (:environment before)
        result (publish fixture) after (resident/snapshot (:context result))
        current (:environment after)]
    (is (not= old current))
    (is (nil? (get-in after [:world :heap (:id old)])))
    (is (= 1 (:rc (m/node (:world before) old))))
    (is (= 2 (:rc (m/node (:world after) current)))) ; context + publication
    (is (identical? before (resident/snapshot context)))
    (let [called (resident/call (:context result) (:file result)
                                hosted/answer-name [nil 42]
                                {:arguments [:erased :nat] :result :nat})]
      (is (= 42 (:value called)))
      (resident/close! (:context called)))
    (resident/close! (:context result)) (resident/close! context)))

(deftest postpublication-adoption-failure-preserves-new-registry-and-owners
  (let [{:keys [context calls] :as fixture}
        (setup :reference :standalone true :bad-adoption? true)
        before (resident/snapshot context)
        error (failure #(publish fixture)) data (ex-data error)
        registration (:resident-source-registration data)
        published (:entry registration)
        world (:checkpoint data)]
    (is (some? error))
    (is (= :adopt-started (:resident-source-phase data)))
    (is (= 1 (count @calls)))
    (is (:success (:resident-source-compiled data)))
    (is (map? published))
    (is (= :released (get-in data [:resident-source-ownership :module-name-state])))
    (is (= :released (get-in data [:resident-source-ownership :prior-environment-in-new-branch])))
    (is (= 1 (:rc (m/node world (:data published)))))
    (is (= 3 (:rc (m/node world (:environment published)))))
    (is (identical? published (get-in world [:source-modules (:module published)])))
    (is (map? (:resident-adoption-entry data)))
    (is (identical? before (resident/snapshot context)))
    (resident/close! context)))
