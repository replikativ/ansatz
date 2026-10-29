(ns prototype.source-import-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json]
            [clojure.java.io :as io] [clojure.string :as str]
            [prototype.source-import :as source] [prototype.source-module :as export]
            [prototype.source-module-test :as model] [prototype.machine :as m]
            [prototype.module-import :as module-import] [prototype.module-import-test :as import-model]
            [prototype.kernel-bridge-test :as guest] [prototype.runtime-prim :as prim]
            [prototype.module-store :as store] [prototype.module-init-capabilities :as init-caps]
            [prototype.import-capabilities :as native-caps]
            [prototype.imported-kernel :as kernel])
  (:import [ansatz.kernel Env]))

(def module model/module-name)
(def digest (apply str (repeat 64 "a")))
(defn fixture
  ([] (fixture (m/world {})))
  ([start]
  (let [[world environment] (m/resource start "compiled-env")
        [world name] (guest/guest-name world "SourceA")
        [world root] (m/allocate world :ctor 0 [])
        f {:params [] :body [:return [:imm 42]]}
        unit {:actions [] :declarations [["answer"]]
              :manifest {:initializationPlan {:module module :imports [] :actions []}}}
        world (-> world (assoc :functions {["answer"] f}
                              :eval-const-authorizations {:units {digest unit} :functions {["answer"] f}})
                  (assoc-in [:kernel-environments (:id root)] {:anchor root :env (Env.)}))
        compiled {:success true :world world :environment environment
                  :envelope {:success true :stage "complete" :mainModule module :moduleSystem false :requestedImports []}
                  :handle {:module-name module :unit-digest digest}}]
    {:world world :compiled compiled :name name :root root})))

(defn part [world data path]
  (let [world (m/retain world data 1)
        [world region] (m/scalar-constructor world 0 [path data] {:objects 2 :usize 3 :ssize 1})
        node (m/node world region)
        node (reduce #(assoc-in %1 [:scalar-bytes %2] 0) node (range 16 41))
        world (m/replace-node world region node)]
    (m/allocate world :ctor 0 [data region])))

(defn invoke [root]
  (fn [world target args]
    (cond
      (= target (:root module-import/helpers)) [(m/retain world root 1) root]
      (= target export/export-helper)
      (let [[env name] args world (-> world (m/release env 1) (m/release name 1))
            [world data] (model/data-value world)
            imports (first (:fields (m/node world data)))
            old (:fields (m/node world imports))
            world (m/replace-node world imports (assoc (m/node world imports) :fields []))
            world (reduce #(m/release %1 %2 1) world old)
            metadata (assoc model/metadata :imports [])
            [world pair] (m/allocate world :ctor 0 [data (json/write-str metadata)])]
        (m/allocate world :ctor 0 [pair]))
      (= target (:part source/helpers)) (part world (first args) (second args))
      (= target (:assemble source/helpers))
      (let [[data _ path] args [world pair] (part world data path)
            region (second (:fields (m/node world pair)))
            [world state] (m/allocate world :ctor 0 [pair])
            [world imports] (m/allocate world :array 246 [])]
        (m/allocate (m/retain world region 1) :ctor 0 [state imports region]))
      :else (throw (ex-info "Unexpected source test helper" {:target target})))))

(deftest authenticated-registration-region-lifetime-and-forks
  (let [{:keys [world compiled name root]} (fixture)
        {:keys [world entry]} (source/register-compiled world (invoke root) compiled name)
        data (:data entry) registered world
        assembled (source/assemble world (invoke root) module name)
        world (:world assembled) key (:key entry)
        region (first (vals (get-in world [:source-regions key :anchors])))
        binding (get (source/make-bindings) "lean_compacted_region_free")
        [freed result] ((:handler binding) {} (m/retain world region 1) [region m/erased])]
    (is (= module (:module entry)))
    (is (nil? (:native-imports world)))
    (is (nil? (:native-source-id (m/node world data))))
    (is (empty? (get-in freed [:source-regions key :anchors])))
    (is (= 0 (second (:fields (m/node freed region)))))
    (is (= data (second (:fields (m/node world region)))))
    (is (some? (m/node freed data)))
    (is (thrown-with-msg? Exception #"Unregistered|freed"
          ((:handler binding) {} freed [region m/erased])))
    (is (thrown-with-msg? Exception #"live region"
          (source/unregister world module)))
    (let [released (source/unregister registered module)]
      (is (empty? (:source-modules released)))
      (is (not (contains? (:heap released) (:id data)))))
    ;; Negative boundary fixture: a persistent region cannot be freed. This
    ;; model's dummy resource entries deliberately are not markPersistent data.
    (let [persistent (assoc-in world [:heap (:id region) :rc] 0)]
      (is (thrown-with-msg? Exception #"Persistent source region"
            ((:handler binding) {} persistent [region m/erased]))))))

(deftest registration-rejects-foreign-id-collisions-and-changed-authority
  (let [{:keys [world compiled name root]} (fixture)]
    (doseq [bad [(assoc-in world [:eval-const-authorizations :units digest] {:actions []})
                 (assoc-in world [:functions ["answer"]] {:params [] :body [:return [:imm 43]]})
                 (assoc-in world [:heap (:id (:environment compiled)) :label] "foreign-same-id")
                 (assoc-in world [:kernel-environments (:id root) :env] (Env.))]]
      (is (thrown? Exception (source/register-compiled bad (invoke root) compiled name))))
    ;; A proper immutable fork shares authenticated receipts/function identities.
    (is (= :ok (let [r (source/register-compiled (assoc world :fork-input 1) (invoke root) compiled name)]
                 (when (:entry r) :ok))))))

(def header-target (:header source/helpers))
(def requests [{:module module :importAll false :isExported true :isMeta false}])
(defn four-constants []
  (let [[world level] (guest/ctor (m/world {}) 1 [guest/nil-tag] 8)
        [world type] (guest/ctor world 3 [level] 8)
        [world a] (guest/compiler-marker world "lcAny" type)
        [world b] (guest/compiler-marker world "lcErased" type)
        [world c] (guest/compiler-marker world "lcVoid" type)
        [world body] (guest/ctor world 3 [guest/nil-tag] 8)
        [world d] (guest/declaration world "answer" type body)]
    [world [a b c d]]))
(defn final-result [world values]
  (let [world (reduce #(m/retain %1 %2 1) world values)
        [world array] (m/allocate world :array 246 values)
        [world root] (m/allocate world :ctor 0 [array])
        [world env] (m/allocate world :ctor 0 [root])]
    (m/allocate world :ctor 0 [env])))
(defn final-invoke [values actual-imports flag]
  (let [delegate (import-model/helper-model (atom []) values)]
    (fn [world target args]
      (cond
        (= target header-target)
        [world (json/write-str {:schema "lean-source-import-header/1" :producer "SourceModuleImport.finalizerHeader"
                               :leanCommit (get prim/pinned-build "lean_get_githash")
                               :moduleSystem false :imports actual-imports})]
        (= target (:quot-init? module-import/helpers)) [world flag]
        :else (delegate world target args)))))

(deftest strict-four-ci-checking-then-native-finalizer-quotient-metadata-projection
  (let [[world values] (four-constants) [world result] (final-result world values)
        opts {:kernel-policy {:allow-compiler-markers? true}
              :finalizer-attestation {:requested-imports requests :header-helper header-target}}
        finished (module-import/finish-finalization world result (final-invoke values requests 1) opts)]
    (is (= :ok (:status finished)))
    (is (= 4 (count (get-in finished [:certificate :constants]))))
    (is (.isQuotEnabled ^Env (get-in finished [:certificate :env])))
    (is (= 4 (count (.allConstants ^Env (get-in finished [:certificate :env])))))
    (doseq [[actual flag expected] [[[] 1 requests] [requests 0 requests] [[] 1 []]]]
      (is (thrown? Exception
            (module-import/finish-finalization world result (final-invoke values actual flag)
              (assoc-in opts [:finalizer-attestation :requested-imports] expected)))))
    (is (thrown? Exception
          (module-import/finish-finalization world result (final-invoke values requests 1)
            (dissoc opts :finalizer-attestation))))))

(defn ordinary-fixture
  ([] (ordinary-fixture (m/world {})))
  ([start]
  (let [{:keys [world compiled] :as base} (fixture start)
        unit (assoc-in (get-in world [:eval-const-authorizations :units digest])
                      [:manifest :initializationPlan :imports]
                      (mapv (fn [i] {:module (:module i) :meta (:isMeta i)}) source/init-requests))
        world (assoc-in world [:eval-const-authorizations :units digest] unit)]
    (assoc base :world world :compiled (-> compiled (assoc :world world)
                                         (assoc-in [:envelope :requestedImports] source/init-requests))))))

(defn ordinary-invoke [root]
  (let [exporter (model/invoke-model (atom []) identity)]
    (fn [world target args]
      (if (= target export/export-helper) (exporter world target args)
        ((invoke root) world target args)))))

(deftest ordinary-registration-preserves-both-implicit-init-imports
  (let [{:keys [world compiled name root]} (ordinary-fixture)
        result (source/register-compiled-over-init world (ordinary-invoke root) compiled name)]
    (is (= :over-init (get-in result [:entry :profile])))
    (is (= source/init-requests (get-in result [:entry :metadata :imports])))
    (is (nil? (:native-source-id (m/node (:world result) (get-in result [:entry :data])))))
    (is (thrown? Exception (source/register-compiled world (ordinary-invoke root) compiled name)))
    (is (thrown-with-msg? Exception #"Standalone assembly"
          (source/assemble (:world result) (ordinary-invoke root) module name)))
    (doseq [imports [[] [source/init-request] (vec (reverse source/init-requests))]]
      (is (thrown? Exception
            (source/register-compiled-over-init world (ordinary-invoke root)
              (assoc-in compiled [:envelope :requestedImports] imports) name))))
    (let [unit (assoc (get-in world [:eval-const-authorizations :units digest]) :actions [{:kind "io-unit"}])
          changed (assoc-in world [:eval-const-authorizations :units digest] unit)]
      (is (thrown? Exception (source/register-compiled-over-init changed (ordinary-invoke root)
                              (assoc compiled :world changed) name))))))

(defn with-tiny-init [f]
  ;; Synthetic module-name/profile fixture around the small verified native DAG.
  ;; Real guest helper/oracle tests remain separate; no full Init graph is loaded.
  (let [lines (str/split-lines (slurp "fixtures/imported-kernel-native.jsonl"))
        manifest (json/read-str (first lines) :key-fn keyword)
        mod (-> (first (get-in manifest [:input :modules]))
                (assoc :module source/init-module
                       :effectiveImport {:module source/init-module :importAll true :isExported false :isMeta false}
                       :hasData true :irPhases "all" :needsIRTrans true))
        manifest (-> manifest (assoc-in [:input :modules] [mod])
                     (assoc-in [:input :requestedImports] source/init-requests)
                     (assoc-in [:input :transitiveClosure] true))
        path (java.io.File/createTempFile "hybrid-init-fixture-" ".jsonl" (io/file "target"))]
    (try
      (spit path (str (json/write-str manifest) "\n" (str/join "\n" (rest lines)) "\n"))
      (let [loaded (store/load-file (m/world {}) (.getPath path))]
        (try (f loaded) (finally (.close ^java.io.Closeable (:source loaded)))))
      (finally (io/delete-file path true)))))

(deftest native-prefix-authentication-and-ownership-preserve-effective-records
  (with-tiny-init
    (fn [loaded]
      (let [calls (atom []) delegate (import-model/helper-model calls (import-model/constants loaded))
            checked (module-import/import-loaded loaded delegate
                      {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})
            current (store/describe-attached (:world checked) (:source loaded))
            prepared (source/prepare-init-prefix current delegate checked)
            world (:world prepared) prefix (:prefix prepared)
            state (:state prefix)
            released (source/release-init-prefix world prefix)]
        (is (= source/init-requests (:producer-imports prefix)))
        (is (= (:modules loaded) (:modules prefix)))
        (is (true? (get-in prefix [:modules 0 :needsIRTrans])))
        (is (false? (get-in prefix [:modules 0 :effectiveImport :isExported])))
        (is (= 1 (:rc (m/node world state))))
        (is (nil? (get-in released [:heap (:id state)])))
        (is (false? @(:closed (:source loaded))))
        (let [child (first (remove #{(:id state)} (keys (:local-nodes prefix))))]
          (is (some? child))
          (is (thrown-with-msg? Exception #"local scaffold changed"
                (source/release-init-prefix (assoc-in world [:heap child :changed] true) prefix))))
        (is (thrown-with-msg? Exception #"source range is shadowed"
              (source/release-init-prefix
                (assoc-in world [:heap (:base (:source loaded))] {:kind :array :fields [] :rc 1}) prefix)))
        (doseq [bad [(assoc prefix :state (m/->Ref 999999))
                     (assoc prefix :constants {})]]
          (is (thrown? Exception (source/release-init-prefix world bad))))
        (is (thrown? Exception (source/release-init-prefix released prefix)))
        (is (thrown-with-msg? Exception #"protected association"
              (source/prepare-init-prefix current delegate (assoc-in checked [:certificate :env] (Env.)))))
        (is (thrown-with-msg? Exception #"descriptors differ"
              (source/prepare-init-prefix (assoc-in current [:modules 0 :needsIRTrans] false) delegate checked)))
        (is (thrown? Exception
              (source/prepare-init-prefix current delegate (assoc-in checked [:certificate :projection-sources] []))))))))

(deftest hybrid-capabilities-route-regions-without-replacing-init-availability
  (let [{:keys [world compiled name root]} (ordinary-fixture)
        registered (source/register-compiled-over-init world (ordinary-invoke root) compiled name)
        world (:world registered) entry (:entry registered) calls (atom [])
        native (merge
                 (into {} (for [[symbol signature] native-caps/signatures]
                            [symbol {:signature signature
                                     :handler (fn [_ world args] (swap! calls conj [symbol args]) [world :native])}]))
                 (init-caps/make-bindings))
        bindings (source/make-hybrid-bindings native)
        [world deps] (m/allocate world :array 246 [])
        [world read] ((get-in bindings ["lean_compacted_region_read" :handler])
                      {:invoke (ordinary-invoke root)} world [m/erased (:key entry) deps m/erased])
        pair (first (:fields (m/node world read)))
        region (second (:fields (m/node world pair)))
        [world _] ((get-in bindings ["lean_compacted_region_free" :handler])
                   {} (m/retain world region 1) [region m/erased])
        [_ native-read] ((get-in bindings ["lean_compacted_region_read" :handler])
                         {} world [m/erased "Init.olean" deps m/erased])]
    (is (identical? (get native "lean_run_mod_init_core") (get bindings "lean_run_mod_init_core")))
    (is (identical? (get native "lean_runtime_mark_persistent") (get bindings "lean_runtime_mark_persistent")))
    (is (= :native native-read))
    (is (= 1 (count @calls)))
    (is (empty? (get-in world [:source-regions (:key entry) :anchors])))
    (is (thrown? Exception
          ((get-in bindings ["lean_compacted_region_read" :handler])
            {} world [m/erased "ansatz-source:unpublished" deps m/erased])))
    (is (= 1 (count @calls)))
    (is (thrown? Exception (source/make-hybrid-bindings (dissoc native "lean_run_mod_init_core"))))))

(defn hybrid-invoke-model
  "Shared bounded helper model; genuine finalizer compatibility is separate."
  [compiled root answer selected finalizer-calls base-invoke final-model]
  (fn [world target args]
              (cond
                (and (= target (:root module-import/helpers)) (= (:environment compiled) (first args)))
                [(m/retain world root 1) root]
                (= target export/export-helper)
                (let [[world io] (base-invoke world target args)
                      pair (first (:fields (m/node world io)))
                      data (first (:fields (m/node world pair)))
                      constants (nth (:fields (m/node world data)) 2)
                      old (first (:fields (m/node world constants)))
                      world (-> world (m/retain answer 1) (m/release old 1)
                                (m/replace-node constants (assoc (m/node world constants) :fields [answer])))]
                  [world io])
                (= target source/hybrid-assemble-helper)
                (let [[prefix data _ path] args
                      [world pair] (part world data path)
                      region (second (:fields (m/node world pair)))
                      [world state] (m/allocate world :ctor 0 [prefix pair])
                      [world imports] (m/allocate world :array 246 [])
                      [world assembly] (m/allocate (m/retain world region 1) :ctor 0 [state imports region])]
                  (m/allocate world :ctor 0 [assembly]))
                (= target (:finalize source/helpers))
                (let [[state imports] args world (-> world (m/release state 1) (m/release imports 1))]
                  (swap! finalizer-calls inc)
                  (final-result world @selected))
                :else (final-model world target args))))

(deftest hybrid-finalization-checks-whole-map-but-receipts-only-source-subset
  (with-tiny-init
    (fn [loaded]
      (let [native-values (import-model/constants loaded)
            native-invoke (import-model/helper-model (atom []) native-values)
            checked (module-import/import-loaded loaded native-invoke
                      {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})
            {:keys [world compiled name root]} (ordinary-fixture (:world checked))
            [world level] (guest/ctor world 1 [guest/nil-tag] 8)
            [world type] (guest/ctor world 3 [level] 8)
            [world body] (guest/ctor world 3 [guest/nil-tag] 8)
            [world answer] (guest/declaration world "answer" type body)
            compiled (assoc compiled :world world)
            requests (conj source/init-requests (first requests))
            final-values (conj native-values answer)
            selected (atom final-values)
            finalizer-calls (atom 0)
            base-invoke (ordinary-invoke root)
            final-model (final-invoke final-values requests 1)
            invoke (hybrid-invoke-model compiled root answer selected finalizer-calls base-invoke final-model)
            registered (source/register-compiled-over-init world invoke compiled name)
            prepared (source/prepare-init-prefix
                       (store/describe-attached (:world registered) (:source loaded)) invoke checked)
            prefix (:prefix prepared)
            assembly (source/assemble-over-init (:world prepared) invoke prefix module name requests)
            finished (source/finalize-over-init assembly invoke 0
                       {:kernel-policy {:allow-axioms? true :allow-unsafe? true
                                        :projection-certificate (:certificate checked)}})
            receipt (:source-import-receipt finished)]
        (is (= :ok (:status finished)))
        (is (= 18 (count (get-in finished [:certificate :constants]))))
        (is (= #{"answer"} (set (map str (keys (:constants receipt))))))
        (is (= #{"answer"} (set (map str (keys (:projected receipt))))))
        (is (= answer (first (vals (:constants receipt)))))
        (is (identical? (get-in finished [:certificate :env]) (:checked-env receipt)))
        (is (= 1 (:rc (m/node (:world finished) (:state prefix)))))
        ;; Completion-only entry preserves the actual IO snapshot and never
        ;; invokes finalization again while checking/attaching its receipt.
        (let [[completed result] (invoke (:world assembly) (:finalize source/helpers)
                                        [(:state assembly) (:imports assembly) 0 m/erased])
              calls @finalizer-calls
              staged (source/finish-over-init assembly completed result invoke
                       {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})]
          (is (= :ok (:status staged)))
          (is (= calls @finalizer-calls))
          (is (m/ref? result))
          (is (some? (m/node completed result)))
          (is (= #{"answer"} (set (map str (keys (get-in staged [:source-import-receipt :projected]))))))
          (is (thrown-with-msg? Exception #"helper identity"
                (source/finish-over-init assembly
                  (assoc-in completed [:functions (:finalize source/helpers)] {:changed true})
                  result invoke {})))
          (is (thrown? Exception
                (source/finish-over-init assembly (dissoc completed :source-import-prefixes) result invoke {}))))
        (is (thrown-with-msg? Exception #"exact ordinary"
              (source/assemble-over-init (:world prepared) invoke prefix module name
                [source/init-request (last requests)])))
        (is (thrown? Exception
              (source/assemble-over-init (dissoc (:world prepared) :source-import-prefixes)
                invoke prefix module name requests)))
        ;; A missing source declaration can still leave a valid checked Init
        ;; environment; it must NOT earn an A import receipt.
        (reset! selected native-values)
        (let [error (try
                      (source/finalize-over-init assembly invoke 0
                        {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})
                      nil (catch clojure.lang.ExceptionInfo cause cause))
              finished (:source-finalization-result (ex-data error))]
          (is (re-find #"published import graph" (.getMessage error)))
          (is (= :ok (:status finished)))
          (is (= 17 (count (get-in finished [:certificate :constants]))))
          (is (m/ref? (:environment finished)))
          (is (some? (m/node (:world finished) (:environment finished))))
          (is (nil? (get-in finished [:world :source-modules module :imports]))))))))

(defn with-delta-hybrid [f]
  (with-tiny-init
    (fn [loaded]
      (let [native-values (import-model/constants loaded)
            checked (module-import/import-loaded loaded (import-model/helper-model (atom []) native-values)
                      {:kernel-policy {:allow-axioms? true :allow-unsafe? true}})
            {:keys [world compiled name root]} (ordinary-fixture (:world checked))
            [world level] (guest/ctor world 1 [guest/nil-tag] 8)
            [world type] (guest/ctor world 3 [level] 8)
            [world body] (guest/ctor world 3 [guest/nil-tag] 8)
            [world answer] (guest/declaration world "answer" type body)
            ;; Independent registry built from reviewed helper objects, never
            ;; copied from the World at an authorization boundary.
            admitted (into {} (map (fn [target] [target {:params [1] :body [:return [:var 1]]}]))
                           (concat (vals module-import/helpers) (vals source/helpers)
                                   [source/hybrid-assemble-helper]))
            world (update world :functions merge admitted)
            compiled (assoc compiled :world world)
            imports (conj source/init-requests (first requests))
            selected (atom (conj native-values answer)) finalizer-calls (atom 0)
            invoke (hybrid-invoke-model compiled root answer selected finalizer-calls
                     (ordinary-invoke root) (final-invoke @selected imports 1))
            registered (source/register-compiled-over-init world invoke compiled name)
            context {:invoke invoke :trusted-functions admitted :bindings {} :trusted-bindings {}}
            current (store/describe-attached (:world registered) (:source loaded))
            prepared (source/prepare-init-prefix-delta context current checked)
            prefix (:prefix prepared)
            assembly (source/assemble-over-init (:world prepared) invoke prefix module name imports)]
        (f {:loaded loaded :checked checked :registered registered :context context
            :current current :prepared prepared :prefix prefix :assembly assembly
            :selected selected :native-values native-values :answer answer
            :name name :imports imports :finalizer-calls finalizer-calls})))))

(deftest explicit-source-delta-route-checks-additions-and-receipts-exact-source-subset
  (with-delta-hybrid
    (fn [{:keys [assembly context prefix checked answer finalizer-calls]}]
      (let [finished (with-redefs [kernel/verify-constants
                                  (fn [& _] (throw (ex-info "Whole Init base rechecked" {})))]
                       (source/finalize-over-init-delta context assembly 0 {}))
            receipt (:source-import-receipt finished)]
        (is (= :ok (:status finished)))
        (is (= 1 @finalizer-calls))
        (is (= 18 (count (get-in finished [:certificate :constants]))))
        (is (= 1 (count (get-in finished [:certificate :new-order]))))
        (is (= #{"answer"} (set (map str (keys (:constants receipt))))))
        (is (= #{"answer"} (set (map str (keys (:projected receipt))))))
        (is (= [answer] (vec (vals (:constants receipt)))))
        (doseq [[name ci] (get-in checked [:certificate :projected])]
          (is (identical? ci (.lookup ^Env (get-in finished [:certificate :env]) name))))
        (is (identical? (get-in finished [:certificate :env]) (:checked-env receipt)))
        (is (= 1 (:rc (m/node (:world finished) (:state prefix)))))
        ;; Completing an independently owned IO result invokes no finalizer.
        (let [[world result] ((:invoke context) (:world assembly) (:finalize source/helpers)
                             [(:state assembly) (:imports assembly) 0 m/erased])
              calls @finalizer-calls
              finished (source/finish-over-init-delta context assembly world result {})]
          (is (= :ok (:status finished)))
          (is (= calls @finalizer-calls))
          (is (= [answer] (vec (vals (get-in finished [:source-import-receipt :constants]))))))))))

(deftest source-delta-rejects-missing-base-refs-helper-changes-and-forged-prefix-capability
  (with-delta-hybrid
    (fn [{:keys [assembly context prefix native-values selected finalizer-calls]}]
      (reset! selected (subvec @selected 1))
      (let [[world result] ((:invoke context) (:world assembly) (:finalize source/helpers)
                           [(:state assembly) (:imports assembly) 0 m/erased])
            calls @finalizer-calls]
        (is (thrown-with-msg? Exception #"delta kernel association failed"
              (source/finish-over-init-delta context assembly world result {})))
        (is (= calls @finalizer-calls))
        (is (thrown-with-msg? Exception #"helper identity"
              (source/finish-over-init-delta context assembly
                (assoc-in world [:functions (:constants module-import/helpers)] {:changed true}) result {})))
        (let [forged (assoc prefix :checked-base {:fabricated true})
              world (assoc-in world [:source-import-prefixes (:id (:state forged))] forged)
              assembly (assoc assembly :prefix forged)]
          (is (thrown-with-msg? Exception #"issued checked-base prefix"
                (source/finish-over-init-delta context assembly world result {}))))
        (is (= calls @finalizer-calls)))
      ;; A valid Init-only checked map still cannot earn a source receipt.
      (reset! selected native-values)
      (let [error (try (source/finalize-over-init-delta context assembly 0 {}) nil
                       (catch clojure.lang.ExceptionInfo cause cause))
            finished (:source-finalization-result (ex-data error))]
        (is (re-find #"published import graph" (.getMessage error)))
        (is (= :ok (:status finished)))
        (is (= 17 (count (get-in finished [:certificate :constants]))))
        (is (nil? (:source-import-receipt finished)))))))

(deftest source-delta-prefix-preflights-authority-and-preserves-prepared-owner-on-capture-failure
  (with-delta-hybrid
    (fn [{:keys [context current checked]}]
      (doseq [target [(:part module-import/helpers) (:constants module-import/helpers)
                      (:quot-init? module-import/helpers)]]
        (let [calls (atom 0)
              context (update context :invoke
                              (fn [invoke] (fn [& args] (swap! calls inc) (apply invoke args))))
              bad (update-in current [:world :functions] assoc target {:changed true})]
          (is (thrown-with-msg? Exception #"helper executable identity"
                (source/prepare-init-prefix-delta context bad checked)))
          (is (zero? @calls))))
      (let [context (update context :invoke
                            (fn [invoke]
                              (fn [world target args]
                                (if (= target (:constants module-import/helpers))
                                  (throw (ex-info "injected capture enumeration failure"
                                                  {:checkpoint world :temporary-owners []}))
                                  (invoke world target args)))))
            error (try (source/prepare-init-prefix-delta context current checked) nil
                       (catch clojure.lang.ExceptionInfo cause cause))
            {:keys [checkpoint prepared-init-prefix prefix-owner temporary-owners]} (ex-data error)
            prefix (:prefix prepared-init-prefix)]
        (is (some? error))
        (is (= prefix (:prefix prefix-owner)))
        (is (identical? checkpoint (:checkpoint prefix-owner)))
        (is (= (:state prefix) (:state prefix-owner)))
        (is (= 1 (:rc (m/node checkpoint (:state prefix)))))
        (is (seq temporary-owners))
        (let [world (reduce #(m/release %1 %2 1) checkpoint temporary-owners)
              world (source/release-init-prefix world prefix)]
          (is (not (contains? (:heap world) (:id (:state prefix))))))))))

(deftest source-delta-receipt-mismatch-preserves-returned-root-owner
  (with-delta-hybrid
    (fn [{:keys [assembly context finalizer-calls]}]
      (let [roots (atom 0) returned (atom nil)
            context (update context :invoke
                            (fn [invoke]
                              (fn [world target args]
                                (if (and (= target (:root module-import/helpers))
                                         (= 3 (swap! roots inc)))
                                  (let [[world root] (m/allocate world :ctor 0 [])]
                                    (reset! returned root) [world root])
                                  (invoke world target args)))))
            error (try (source/finalize-over-init-delta context assembly 0 {}) nil
                       (catch clojure.lang.ExceptionInfo cause cause))
            {:keys [checkpoint source-receipt-temporary-owners temporary-owners source-finalization-result]} (ex-data error)]
        (is (some? error))
        (is (re-find #"association differs" (.getMessage error)))
        (is (= 1 @finalizer-calls))
        (is (= [@returned] source-receipt-temporary-owners temporary-owners))
        (is (= 1 (:rc (m/node checkpoint @returned))))
        (is (= :ok (:status source-finalization-result)))
        (is (= (:heap (:world source-finalization-result))
               (:heap (m/release checkpoint @returned 1))))))))
