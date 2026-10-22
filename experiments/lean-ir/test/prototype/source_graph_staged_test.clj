(ns prototype.source-graph-staged-test
  "Staged graph receipt tests. Actual G1 assembler and Java whole checking;
   native-prefix constructors, finalizer, header/index/witness are explicit models.
   No genuine frontend chain or old/new mkOwnedPart coexistence is claimed."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.runtime-string :as string]
            [prototype.source-graph-runtime-test :as publication]
            [prototype.source-graph-helper-test :as helper]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.eval-const :as eval]
            [prototype.kernel-host :as kernel-host]
            [prototype.imported-kernel :as imported]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.expr :as expression]
            [clojure.walk :as walk]
            [prototype.source-module-test :as module-model]
            [prototype.machine :as m]
            [prototype.module-import :as imports]
            [prototype.source-import :as source]
            [prototype.resident-init-prefix :as graph]
            [prototype.resident-frontend :as resident]
            [prototype.raw-interop :as raw]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as record]
            [prototype.guest-encoding :as encoding]
            [prototype.frontend :as frontend]
            [prototype.runtime-prim :as prim])
  (:import [ansatz.kernel Name]))

(def diagnostics (atom []))
(defn remember! [state label packet]
  (swap! state update :packets conj [label packet]) packet)
(defn fields [world value] (:fields (m/node world value)))
(defn array! [world values] (m/allocate world :array 246 (vec values)))
(defn packed! [world values bytes flags]
  (let [[world value] (record/ctor world 0 values bytes)]
    [(reduce-kv #(record/scalar! %1 value %2 "uint8" %3) world flags) value]))
(defn copy-array! [world values]
  (array! (reduce #(m/retain %1 %2 1) world values) values))
(defn wire-name [^Name value]
  (cond (.isAnonymous value) ["anonymous"]
        (.isStr value) ["str" (wire-name (.prefix value)) (.str value)]
        :else ["num" (wire-name (.prefix value)) (str (.num value))]))

(defn model-index-name [wire]
  ;; This tiny fixture has string-only declaration names. Validate length before
  ;; scanning/building Java Names; no numeric parsing or unbounded recursion.
  (loop [wire wire parts [] chars 0]
    (when (>= (count parts) 64) (throw (ex-info "Modeled index Name exceeds depth" {})))
    (if (= ["anonymous"] wire)
      (reduce #(Name/mkStr %1 %2) Name/ANONYMOUS_NAME (rseq parts))
      (let [[tag parent part] (when (and (vector? wire) (= 3 (count wire))) wire)]
        (when-not (and (= "str" tag) (string? part) (<= (+ chars (count part)) 512))
          (throw (ex-info "Modeled index requires a bounded string-only Name" {})))
        (recur parent (conj parts part) (+ chars (count part)))))))

(defn model-metadata-text [description]
  (let [text (json/write-str (update description :indices
                              #(mapv (fn [[name index]] [(wire-name name) index]) %)))]
    (when (> (count text) 32768) (throw (ex-info "Modeled Environment metadata exceeds bound" {})))
    text))

(defn model-environment-metadata [world environment]
  (let [node (m/node world environment) values (:fields node)
        text (second values)]
    (when-not (and (= :ctor (:kind node)) (= 2 (count values)) (string? text) (<= (count text) 32768))
      (throw (ex-info "Source model Environment lacks its owned metadata payload" {})))
    (let [decoded (#'graph/graph-json! text {:max-bytes 32768}
                    (assoc publication/graph-limits :max-name-nodes 64))
          {:keys [requests modules indices]} decoded]
      (when-not (and (map? decoded) (= 3 (count decoded))
                     (= #{:requests :modules :indices} (set (keys decoded)))
                     (vector? requests) (<= (count requests) 16)
                     (vector? modules) (<= 1 (count modules) 16)
                     (every? #(and (string? %) (<= (count %) 512)) modules)
                     (vector? indices) (<= (count indices) 64))
        (throw (ex-info "Modeled Environment metadata exceeds collection bounds" {})))
      (assoc decoded :indices
        (reduce (fn [out row]
                  (when-not (and (vector? row) (= 2 (count row))
                                 (integer? (second row)) (<= 0 (second row)) (< (second row) (count modules)))
                    (throw (ex-info "Modeled Environment index row differs" {})))
                  (let [name (model-index-name (first row))]
                    (when (contains? out name) (throw (ex-info "Duplicate modeled Environment index" {})))
                    (assoc out name (second row)))) {} indices)))))

(defn assembled-records!
  "Read ONLY the assembler-returned Raw map. Fixed pinned Raw/AssocList layout;
   bounded bucket/entry walk rejects duplicate keys/cycles/inconsistent size."
  [world assembled]
  (let [map (first (fields world assembled)) map-node (m/node world map)
        _ (when-not (bridge/constructor-layout? map-node 2 0)
            (throw (ex-info "Staged fixture assembled map has another Raw layout" {})))
        [size buckets] (:fields map-node) bucket-node (m/node world buckets)
        _ (when-not (and (integer? size) (<= 0 size 16) (= :array (:kind bucket-node))
                         (<= (count (:fields bucket-node)) 1024))
            (throw (ex-info "Staged fixture assembled map exceeds declared bounds" {})))
        result
        (reduce (fn [out bucket]
                  (loop [out out cursor bucket]
                    (if (= cursor (m/->Tag 0)) out
                      (let [node (m/node world cursor)]
                        (when-not (and (< (count out) size) (= 1 (:tag node))
                                       (bridge/constructor-layout? node 3 0))
                          (throw (ex-info "Staged fixture has malformed or cyclic reachable map bucket" {})))
                        (let [[key value tail] (:fields node)
                              name (bridge/project-name-bounded world key {:max-nodes 64 :max-chars 512})
                              imported (m/node world value)
                              _ (when-not (bridge/constructor-layout? imported 3 1)
                                  (throw (ex-info "Staged fixture map value has another ImportedModule layout" {})))
                              effective (first (:fields imported))
                              _ (when-not (bridge/constructor-layout? (m/node world effective) 1 2)
                                  (throw (ex-info "Staged fixture map value has another EffectiveImport layout" {})))
                              request (first (fields world effective))
                              _ (when-not (bridge/constructor-layout? (m/node world request) 1 3)
                                  (throw (ex-info "Staged fixture map value has another Import layout" {})))
                              actual (bridge/project-name-bounded world (first (fields world request))
                                                                 {:max-nodes 64 :max-chars 512})]
                          (when (or (contains? out name) (not= actual name))
                            (throw (ex-info "Staged fixture reachable map has duplicate/mismatched module key" {})))
                          (recur (assoc out name {:node imported :reference value}) tail))))))
                {} (:fields bucket-node))]
    (when-not (= size (count result))
      (throw (ex-info "Staged fixture reachable map size differs" {})))
    result))

(defn configure-staged
  "Build one isolated test configuration BEFORE any graph profile/prefix exists.
   Only fixed modeled empty source/G1 roots are replaced; already present real
   bodies remain exact objects. No old real mkOwnedPart export is installed."
  [{:keys [functions bindings checked modules operations snapshot]}]
  (let [state (atom {:packets [] :environments {} :headers []})
        source-part (:part source/helpers) assembler @#'graph/graph-assemble-helper
        _ (doseq [target [source-part assembler]]
            (when-not (= {:params [] :body [:return [:imm 0]]} (get functions target))
              (throw (ex-info "Staged fixture requires only an empty modeled helper placeholder" {}))))
        existing (dissoc functions source-part assembler)
        catalogue @helper/bundle
        added (ir/load-closure catalogue (vec (keys (:declarations catalogue)))
                               #(abi/lower-catalogue catalogue %) {:existing-functions existing})
        functions (merge existing added)
        _ (doseq [[target body] existing]
            (when-not (identical? body (get functions target))
              (throw (ex-info "Staged fixture replaced a captured real executable" {}))))
        invoke (fn [context world target args]
                 (let [[world value] ((:invoke context) world target args)]
                   (remember! state :nested-helper {:world world :value value}) [world value]))
        encode (fn [context world text]
                 (let [[encoded name] (encoding/encode-name world #(invoke context %1 %2 %3) (Name/fromString text))
                       ;; unwrap deliberately clears :result for a top-level
                       ;; caller. This adapter runs INSIDE a raw handler, whose
                       ;; parent control packet must stay unchanged. Restore
                       ;; ONLY that documented result field, not other controls.
                       restored (if (contains? world :result) (assoc encoded :result (:result world))
                                    (dissoc encoded :result))]
                   (remember! state :encoded-name {:world restored :name name})
                   [restored name]))
        native-description (fn [] {:requests source/init-requests :modules @modules
                                   :indices (zipmap (keys (get-in checked [:certificate :constants])) (repeat 0))})
        metadata (fn [world environment]
                   (if (= 1 (count (fields world environment)))
                     (if (= environment (:environment snapshot)) (native-description)
                       (throw (ex-info "Unknown one-field modeled Environment" {})))
                     (model-environment-metadata world environment)))
        decorate (fn [world environment]
                   (let [node (m/node world environment)]
                     (when-not (and (= :ctor (:kind node)) (= 1 (count (:fields node)))
                                    (not (m/native-reference? world environment)))
                       (throw (ex-info "Compiled Environment decoration requires the exact local model layout" {})))
                     [(m/replace-node world environment
                        (assoc node :fields (conj (vec (:fields node)) (model-metadata-text (native-description)))))
                      environment]))
        specs
        {(:request imports/helpers)
         [4 "object" false
          (fn [context world [text all exported meta]]
            (let [[world name] (encode context world text)]
              (packed! world [name] 3 {0 all 1 exported 2 meta})))]
         (:module imports/helpers)
         [9 "object" false
          (fn [context world [text all exported meta phases data? trans? parts ir-parts]]
            (let [[world name] (encode context world text)
                  [world request] (packed! world [name] 3 {0 all 1 exported 2 meta})
                  [world effective] (packed! world [request] 2 {0 phases 1 data?})]
              (packed! world [effective parts ir-parts] 1 {0 trans?})))]
         (:state imports/helpers)
         [1 "object" false
          (fn [context world [array]]
            (let [records (fields world array)
                  [world buckets] (array! world (repeat 16 (m/->Tag 0)))
                  [world empty-map] (m/allocate world :ctor 0 [0 buckets])
                  [world map names]
                  (reduce (fn [[world map names] imported]
                            (let [effective (first (fields world imported))
                                  request (first (fields world effective))
                                  name (first (fields world request))
                                  world (-> world (m/retain name 2) (m/retain imported 1))
                                  [world map] (invoke context world @helper/insert-helper [map name imported])]
                              [world map (conj names name)])) [world empty-map []] records)
                  [world names] (array! world names)
                  world (m/release world array 1)]
              (m/allocate world :ctor 0 [map names])))]
         (:finalize source/helpers)
         [4 "object" false
          (fn [_ world [assembled requests options _]]
            (let [order (mapv #(bridge/project-name world %) (fields world (second (fields world assembled))))
                  records (assembled-records! world assembled)
                  data (mapv (fn [name]
                               (let [imported (:node (get records name))
                                     parts (second (:fields imported))
                                     part (first (fields world parts))]
                                 (first (fields world part)))) order)
                  constants (vec (mapcat #(fields world (nth (fields world %) 2)) data))
                  [world values] (copy-array! world constants)
                  [world root] (m/allocate world :ctor 0 [values])
                  encoded-requests (mapv (fn [request]
                                          (let [node (m/node world request)]
                                            {:module (wire-name (bridge/project-name world (first (:fields node))))
                                             :importAll (= 1 (m/read-scalar-node node {:index 1 :offset 0 :type "uint8" :region :scalar}))
                                             :isExported (= 1 (m/read-scalar-node node {:index 1 :offset 1 :type "uint8" :region :scalar}))
                                             :isMeta (= 1 (m/read-scalar-node node {:index 1 :offset 2 :type "uint8" :region :scalar}))}))
                                        (fields world requests))
                  indices (reduce-kv (fn [out index data]
                                       (reduce (fn [out name] (if (contains? out name) out (assoc out name index)))
                                               out (map #(bridge/project-name world %)
                                                        (concat (fields world (nth (fields world data) 1))
                                                                (fields world (nth (fields world data) 3)))))) {} data)
                  description {:requests encoded-requests :modules (mapv str order) :indices indices}
                  ;; Explicit model layout: root plus immutable owned text.
                  ;; Mutable/JVM preserve guest fields, not arbitrary World keys.
                  [world environment] (m/allocate world :ctor 0 [root (model-metadata-text description)])
                  _ (swap! state assoc-in [:environments (:id environment)] description)
                  world (-> world (m/release assembled 1) (m/release requests 1))
                  [world io] (m/allocate world :ctor 0 [environment])]
              (remember! state :modeled-finalizer {:world world :io io :data data})
              [world io]))]
         (:header source/helpers)
         [1 "object" true
          (fn [_ world [environment]]
            [world (json/write-str {:schema "lean-source-import-header/1" :producer "SourceModuleImport.finalizerHeader"
                                   :leanCommit (get prim/pinned-build "lean_get_githash") :moduleSystem false
                                   :imports (:requests (metadata world environment))})])]
         @#'graph/module-names-helper
         [1 "object" true
          (fn [context world [environment]]
            (let [[world names] (reduce (fn [[world names] text]
                                         (let [[world name] (encode context world text)] [world (conj names name)]))
                                       [world []] (:modules (metadata world environment)))]
              (array! world names)))]
         @#'graph/module-index-helper
         [2 "tobject" true
          (fn [_ world [environment name]]
            (if-let [index (get-in (metadata world environment) [:indices (bridge/project-name world name)])]
              (m/allocate world :ctor 1 [index]) [world (m/->Tag 0)]))]
         frontend/header-target
         [3 "object" false
          (fn [_ world [_ filename _]]
            (m/allocate world :ctor 0 [(json/write-str
              {:schema "lean-file-header/1" :producer "RuntimeCompileShim.inspectFileHeader"
               :leanCommit (get prim/pinned-build "lean_get_githash")
               :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
               :fileName (string/string-value {:ref? m/ref? :node m/node} world filename) :moduleSystem false :hasErrors false :headerEndByte 0 :diagnostics []
               :requestedImports (or (peek (:headers @state)) source/init-requests)})]))]}
        bindings (reduce-kv
                   (fn [out target [arity ret borrow handler]]
                     (let [symbol (str "graph_staged_model_" (pr-str target))]
                       (assoc out symbol {:signature {:params (vec (repeat arity {:ty "object" :borrow borrow}))
                                                     :return-type ret}
                                          :handler (fn [context world args]
                                                     (swap! operations conj target)
                                                     (handler context world args))}))) bindings specs)
        bindings (update-in bindings [(str "graph_staged_model_" (pr-str (:finalize source/helpers))) :signature :params 2]
                            assoc :borrow true)
        functions (reduce-kv
                    (fn [out target [arity _ _ _]]
                      (let [symbol (str "graph_staged_model_" (pr-str target))
                            params (vec (range 1 (inc arity))) result (inc arity)]
                        (assoc out target {:params params :raw-extern {:symbol symbol :signature (:signature (get bindings symbol))}
                                           :body [:host symbol (mapv #(vector :var %) params) result [:return [:var result]]]})))
                    functions specs)
        witness (publication/str-name "GraphFixtureWitness")
        witness-rows (mapv #(assoc % :sourceModule (publication/str-name "EmptyGraphA") :sourceLocal false)
                           (rest (mapv #(json/read-str % :key-fn keyword)
                                       (str/split-lines (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl")))))
        answer (publication/str-name "answer")
        witness-text (json/write-str {:schema "lean-eval-const-witness/1"
                                      :producer "RuntimeCompileShim.exportEvalConstWitness"
                                      :leanCommit (get prim/pinned-build "lean_get_githash")
                                      :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                                      :name answer :boxedTarget ["str" answer "_boxed"] :sorryDep nil
                                      :missingDependencies [] :declarations witness-rows})
        probe (publication/str-name "GraphImportedProbe")
        apply-probe (publication/str-name "GraphImportedApply")
        functions (assoc functions
                    apply-probe {:params [1 2] :body [:call 3 [:closure [:var 1]]
                                                     [[:imm m/erased] [:var 2]] [:return [:var 3]]]}
                    witness {:params [1 2 3] :body [:dec [:var 1] 1 [:dec [:var 2] 1
                                                    [:let 4 [:ctor 0 [[:imm witness-text]]] [:return [:var 4]]]]]}
                    probe {:params [1 2 3 4] :body [:host "lean_eval_const" [[:var 1] [:var 2] [:var 3] [:var 4]] 5
                                                                  [:return [:var 5]]]})]
    {:functions functions :bindings bindings :state state :checked checked :probe probe :apply-probe apply-probe
     :decorate-compiled-environment decorate}))

(def budgets {:outer-fuel 1000000 :helper-fuel 1000000 :attempt-fuel 100000000})
(def policy {:allow-axioms? true :allow-unsafe? true})
(defn publish! [{:keys [context prefix profile compile-model request]}]
  (with-redefs [prototype.resident-source/load-and-publish-graph compile-model]
    (graph/publish-source-graph-node context request prefix profile []
      {:proof-budgets (select-keys budgets [:helper-fuel :attempt-fuel])})))
(defn consumer-request [name]
  {:text "import EmptyGraphA\n" :file-name name :module-name (Name/fromString "GraphConsumer")
   :roots [] :initialization :defer})
(def consumer-imports
  (conj source/init-requests (assoc source/init-request :module (publication/str-name "EmptyGraphA"))))
(defn prepare! [{:keys [prefix profile transport]} publication]
  (swap! (:state transport) update :headers conj consumer-imports)
  (graph/prepare-source-graph-import (:context publication) (consumer-request "GraphConsumer.lean")
    prefix profile [(:graph-node publication)] {:kernel-policy policy :budgets budgets}))
(defn complete-io! [control]
  (loop [n 0]
    (when (> n 20) (throw (ex-info "Staged fixture exceeded bounded finalizer slices" {})))
    (let [result (graph/advance-source-graph-import! control {:max-operations 4 :wall-ms 1000})]
      (if (= :io-completed (get-in result [:progress :phase])) result (recur (inc n))))))
(defn imported-call! [fixture packet]
  (let [node-name (publication/str-name "EmptyGraphA")
        node (get-in packet [:world :source-modules node-name])
        ;; Borrow the real sealed Name owned by the published ModuleData; the
        ;; raw eval ABI borrows Environment,Options,Name.
        own-node (#'graph/graph-node! (:node-cap fixture))
        name (get-in own-node [:wire-names (publication/str-name "answer")])
        result (raw/call (:session packet) (:world packet) (get-in fixture [:transport :probe])
                        [m/erased (:environment packet) (:options packet) name])]
    (remember! (get-in fixture [:transport :state]) :public-eval result)
    result))
(defn failure [f] (try (f) nil (catch Throwable cause cause)))

(deftest actual-assembler-one-node-completion-activates-public-imported-row
  (doseq [backend [:reference :mutable :jvm]]
    (publication/with-empty-publication backend
    (fn [{:keys [context prefix transport captured configuration issued-install-options] :as fixture}]
      (let [before (resident/snapshot context) published (publish! fixture)
            _ (swap! captured conj (:context published))
            fixture (assoc fixture :node-cap (:graph-node published))
            published-packet (resident/snapshot (:context published))
            denied (failure #(imported-call! fixture published-packet))
            _ (remember! (:state transport) :before-completion-denial denied)
            prepared (prepare! fixture published) control (:control prepared)
            cross-old (failure #(graph/advance-import! control {:max-operations 1 :wall-ms 1000}))
            advanced (complete-io! control)
            result (graph/finish-source-graph-import! control)
            _ (remember! (:state transport) :successful-finish result)
            packet (resident/snapshot (:context result))
            called (imported-call! fixture packet)
            wrapper (m/node (:state called) (:value called))
            _ (when-not (and (= 1 (:tag wrapper)) (bridge/constructor-layout? wrapper 1 0))
                (throw (ex-info "Public eval did not return an owned Except.ok closure" {})))
            closure (first (:fields wrapper))
            closure-node (m/node (:state called) closure)
            _ (when-not (and (= :closure (:kind closure-node))
                             (= ["str" (publication/str-name "answer") "_boxed"] (:function closure-node)))
                (throw (ex-info "Public eval returned another boxed closure" {})))
            apply-world (-> (:state called) (m/retain closure 1) (m/release (:value called) 1) (assoc :result 0))
            _ (remember! (:state transport) :owned-closure-before-apply
                         {:world apply-world :session (:session called) :closure closure})
            answer (raw/call (:session called) apply-world (:apply-probe transport) [closure 41])
            _ (remember! (:state transport) :identity-answer answer)
            progress (:progress result)
            receipt-cap (get-in packet [:world :source-modules (publication/str-name "EmptyGraphA") :graph-import])
            receipt (#'graph/graph-receipt! receipt-cap)]
        (is (false? (identical? issued-install-options (get-in configuration [:frontend-configuration :install-options]))))
        (is (some? denied))
        (is (= "Source import lacks checked module installation authority" (.getMessage ^Throwable denied)))
        (is (some? cross-old))
        (is (= 41 (:value answer)))
        (is (= 1 (count (:graph-import-receipts result))))
        (is (= :finished (:phase progress)))
        (is (= (:guest-steps progress) (+ (:outer-steps progress) (:helper-steps progress))))
        (is (> (:helper-steps progress) (get-in advanced [:progress :helper-steps])))
        (is (true? (.get ^java.util.concurrent.atomic.AtomicBoolean (:activation receipt))))
        (is (some? (failure #(graph/finish-source-graph-import! control))))
        (is (some? (failure #(graph/finish-import! control))))
        (is (true? (identical? before (resident/snapshot context))))
        (is (nil? (get-in published-packet [:world :source-modules (publication/str-name "EmptyGraphA") :graph-import])))
        (resident/close! (:context result))))
    :local-ci? true :configure configure-staged
    :configuration-change #(update-in % [:frontend-configuration :install-options] (fn [options] (into {} options))))))

(deftest post-adoption-failure-keeps-registered-batch-inactive-on-public-paths
  (publication/with-empty-publication :reference
    (fn [{:keys [transport captured configuration prefix profile request compiler-calls compile-model] :as fixture}]
      (let [published (publish! fixture) _ (swap! captured conj (:context published))
            fixture (assoc fixture :node-cap (:graph-node published))
            prepared (prepare! fixture published) control (:control prepared)
            _ (complete-io! control)
            selected (ex-info "selected post-adoption return construction failure" {})
            cause (with-redefs-fn {#'graph/finished-import-state (fn [_] (throw selected))}
                    #(failure (fn [] (graph/finish-source-graph-import! control))))
            state (:source-graph-import-state (ex-data cause))
            _ (remember! (:state transport) :failed-staged-finish {:cause cause :state state})
            candidate (get-in state [:source-graph :batch-candidate-world])
            cap (get-in candidate [:source-modules (publication/str-name "EmptyGraphA") :graph-import])
            registered (locking @#'graph/graph-receipts (.get ^java.util.WeakHashMap @#'graph/graph-receipts cap))
            adopted (:adopted-context state)
            _ (remember! (:state transport) :failed-adopted-context adopted)
            packet (resident/snapshot adopted)
            getter-before (count @(get fixture :operations))
            denied (failure #(imported-call! fixture packet))
            _ (remember! (:state transport) :inactive-public-denial denied)
            getter-after (count @(get fixture :operations))
            before-compiles @compiler-calls
            parent-denied
            (with-redefs [prototype.resident-source/load-and-publish-graph compile-model]
              (failure #(graph/publish-source-graph-node adopted
                          (assoc request :text "import EmptyGraphA\n" :file-name "GraphChild.lean"
                                 :module-name (Name/fromString "GraphChild"))
                          prefix profile [(:graph-node published)]
                          {:proof-budgets (select-keys budgets [:helper-fuel :attempt-fuel])})))]
        (remember! (:state transport) :inactive-parent-denial parent-denied)
        (is (some? cause)) (is (true? (identical? selected (.getCause cause))))
        (is (some? registered))
        (is (false? (.get ^java.util.concurrent.atomic.AtomicBoolean (:activation registered))))
        (is (some? denied))
        (is (= "Source import lacks checked module installation authority" (.getMessage ^Throwable denied)))
        (is (= getter-before getter-after))
        (is (some? parent-denied))
        (is (= "Expected an issued completed source graph receipt" (.getMessage ^Throwable parent-denied)))
        (is (= before-compiles @compiler-calls))
        (is (true? (identical? cause (failure #(graph/finish-source-graph-import! control)))))
        (is (some? adopted))
        (is (nil? (get-in (resident/snapshot (:context published))
                         [:world :source-modules (publication/str-name "EmptyGraphA") :graph-import])))
        ;; Expected failure packets remain in diagnostics, including the adopted
        ;; Context. Outer fixture owns and closes its native Source at teardown.
        (swap! diagnostics conj {:fixture fixture :cause cause :state state})))
    :local-ci? true :configure configure-staged))

(deftest graph-helper-failure-accounting-preserves-known-charge-and-unknown-reservation
  (let [target (publication/str-name "GraphFailedHelper")
        functions {target {:params [] :body [:let 1 [:literal 0] [:host "graph_fixture_observed_failure" [] 2 [:return [:var 2]]]]}}
        selected-known (ex-info "known boundary graph fixture helper failure" {})
        bindings {"graph_fixture_observed_failure"
                  {:signature {:params [] :return-type "object"}
                   :handler (fn [& _] (throw selected-known))}}
        world (m/world functions)
        session (raw/open-functions functions bindings {:backend :reference :fuel 10})
        make-state #(atom {:world world :session session :used 0 :helper-steps 0 :reserved 0 :graph-operation? true})
        known (make-state)
        cause (failure #((#'graph/graph-invocation known {:helper-fuel 10 :attempt-fuel 20}) world target []))]
    (swap! diagnostics conj {:scope :known-helper-failure :cause cause :state @known})
    (is (some? cause) "known cause") (is (true? (:budget-poisoned? @known)) "known poison")
    (is (true? (identical? selected-known (.getCause ^Throwable cause))) "known actual host cause")
    (is (= 2 (:used @known)) "known two executed instructions")
    (is (true? (identical? (:world @known) (:checkpoint (ex-data cause)))) "known checkpoint identity")
    (is (true? (identical? (:session @known) (:checkpoint-session (ex-data cause)))) "known session identity")
    (is (= (:used @known) (- (get-in (ex-data cause) [:checkpoint :stats :steps])
                            (get-in world [:stats :steps]))) "known checkpoint delta")
    (is (= (:used @known) (:helper-steps @known)) "known helper charge")
    (is (zero? (:reserved @known)) "known reservation cleared")
    (let [unknown (make-state) selected (ex-info "unobserved graph fixture helper failure" {})
          cause (with-redefs [raw/call (fn [& _] (throw selected))]
                  (failure #((#'graph/graph-invocation unknown {:helper-fuel 10 :attempt-fuel 20}) world target [])))]
      (swap! diagnostics conj {:scope :unknown-helper-failure :cause cause :state @unknown})
      (is (true? (identical? selected cause)) "unknown cause identity")
      (is (zero? (:used @unknown)) "unknown unobserved charge") (is (zero? (:helper-steps @unknown)) "unknown helper charge")
      (is (= 10 (:reserved @unknown)) "unknown reservation retained") (is (true? (:budget-poisoned? @unknown)) "unknown poison"))))

(deftest graph-operation-api-rejects-forged-control-before-hashing
  (doseq [control [publication/poison {} nil]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (graph/advance-source-graph-import! control {:max-operations 1 :wall-ms 1})))
    (is (thrown? clojure.lang.ExceptionInfo (graph/finish-source-graph-import! control)))))

(deftest public-publication-rejects-missing-or-replaced-fixed-installer-before-guest-work
  (doseq [change [(fn [configuration] (update configuration :frontend-configuration dissoc :install-options))
                  (fn [configuration] (assoc-in configuration
                                         [:frontend-configuration :install-options :authorize-source-import]
                                         source/authorize-imported-row))
                  (fn [configuration] (assoc-in configuration [:frontend-configuration :install-options :initialize?] true))
                  (fn [configuration] (update-in configuration [:frontend-configuration :install-options :witness]
                                          #(mapv identity %)))
                  (fn [configuration] (assoc-in configuration [:frontend-configuration :install-options :witness-format] :typed-ir))]]
    (publication/with-empty-publication :reference
      (fn [{:keys [operations compiler-calls] :as fixture}]
        (let [before (count @operations) cause (failure #(publish! fixture))]
          (swap! diagnostics conj {:scope :fixed-installer-rejection :cause cause})
          (is (some? cause))
          (is (= "Source graph requires its exact completed installer and witness" (.getMessage ^Throwable cause)))
          (is (zero? @compiler-calls))
          (is (= before (count @operations)))))
      :configuration-change change)))


(deftest actual-file-decoder-reexports-completed-A-through-fixed-graph-installer
  ;; A legitimate empty B file requests imported A.answer as its exported root.
  ;; No B-owned CI/IR or genuine Lean compiler execution is claimed here.
  (publication/with-empty-publication :reference
    (fn [{:keys [configuration issued-install-options transport captured] :as fixture}]
      (let [published (publish! fixture)
            _ (swap! captured conj (:context published))
            prepared (prepare! fixture published)
            _ (complete-io! (:control prepared))
            completed (graph/finish-source-graph-import! (:control prepared))
            _ (remember! (:state transport) :completed-A completed)
            packet (resident/snapshot (:context completed))
            world (:world packet) module-a (publication/str-name "EmptyGraphA")
            module-b (publication/str-name "GraphReexportB")
            answer (publication/str-name "answer")
            node (#'graph/graph-node! (:graph-node published))
            name (get-in node [:wire-names answer])
            a-digest (get-in world [:eval-const-authorizations :unit-digests answer])
            a-unit (get-in world [:eval-const-authorizations :units a-digest])
            a-function (get-in world [:functions answer])
            a-row (get-in world [:eval-const-authorizations :declarations answer])
            rows (mapv #(json/read-str % :key-fn keyword)
                       (str/split-lines (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl")))
            manifest (-> (first rows) (assoc-in [:initializationPlan :module] module-b)
                         (assoc-in [:initializationPlan :imports]
                           (mapv #(hash-map :module (:module %) :meta (:isMeta %)) consumer-imports)))
            imported (mapv #(assoc % :sourceModule module-a :sourceLocal false) (rest rows))
            bundle (str/join "\n" (map json/write-str (into [manifest] imported)))
            envelope {:schema "lean-file-compilation/1" :producer "RuntimeCompileShim.compileImportedFileState"
                      :leanCommit (get prim/pinned-build "lean_get_githash")
                      :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                      :fileName "GraphReexportB.lean" :mainModule module-b :moduleSystem false
                      :requestedImports consumer-imports :success true :stage "complete"
                      :environmentState "after-commands" :diagnostics [] :bundle bundle}
            ;; Model only the serialized compiler IO. Env is the real completed
            ;; A checked Env, correct for an empty B file importing A.
            [world roots] (array! (m/retain world name 1) [name])
            [world pair] (m/allocate (m/retain world (:environment packet) 1) :ctor 0
                                   [(:environment packet) (json/write-str envelope)])
            [world io] (m/allocate world :ctor 0 [pair])
            raw-result {:state (assoc world :status :done :result io) :value io :session (:session packet)}
            _ (remember! (:state transport) :modeled-B-compiler-IO raw-result)
            observed (atom []) install @#'eval/install-file-bundle
            expected (get-in configuration [:frontend-configuration :install-options :authorize-source-import])
            installed
            (with-redefs [eval/install-file-bundle
                          (fn [context world environment roots bundle options]
                            (swap! observed conj {:checkpoint? (fn? (:checkpoint! context))
                                                  :same-authorizer? (identical? expected (:authorize-source-import options))})
                            (let [invoke (:invoke context)]
                              (install (assoc context :invoke
                                         (fn [world target args]
                                           (swap! observed conj {:target target})
                                           (invoke world target args)))
                                       world environment roots bundle options)))]
              (frontend/finish-compilation-refs raw-result {:file-name "GraphReexportB.lean" :roots roots}
                                                (:frontend-configuration configuration)))
            _ (remember! (:state transport) :actual-B-decoder-install installed)
            digest (get-in installed [:handle :unit-digest])
            unit (get-in installed [:world :eval-const-authorizations :units digest])
            ;; Drop the original inherited Env owner in THIS new branch; the
            ;; decoder's retained returned Env remains owned. Caller owns roots.
            cleaned (-> (:world installed) (m/release (:environment packet) 1) (m/release roots 1))
            next-packet (assoc packet :world cleaned :session (:session installed)
                                     :environment (:environment installed))
            context (resident/adopt-prepared next-packet configuration)
            _ (remember! (:state transport) :B-adopted-context context)
            file (resident/->FileHandle digest unit (Name/fromString "GraphReexportB"))
            called (resident/call context file (Name/fromString "answer") [nil 41]
                                 {:arguments [:erased :nat] :result :nat})
            _ (remember! (:state transport) :B-public-file-call called)]
        (is (true? (:sourceLocal a-row)))
        (is (every? #(false? (:sourceLocal %)) imported))
        (is (false? (identical? issued-install-options (get-in configuration [:frontend-configuration :install-options]))))
        (is (every? true? (map :checkpoint? (filter #(contains? % :checkpoint?) @observed))))
        (is (every? true? (map :same-authorizer? (filter #(contains? % :same-authorizer?) @observed))))
        (is (pos? (count (filter #(= (publication/str-name "GraphFixtureWitness") (:target %)) @observed))))
        (is (pos? (count (filter #(= @#'graph/module-index-helper (:target %)) @observed))))
        (is (= module-b (get-in unit [:manifest :initializationPlan :module])))
        (is (= [] (:declarations unit))) (is (= [] (:actions unit)))
        (is (not= a-digest digest))
        (is (true? (identical? a-unit (get-in installed [:world :eval-const-authorizations :units a-digest]))))
        (is (true? (identical? a-function (get-in installed [:world :functions answer]))))
        (is (true? (identical? a-row (get-in installed [:world :eval-const-authorizations :declarations answer]))))
        (is (= 41 (:value called)))
        (doseq [context [(:context called) context (:context completed)]] (resident/close! context))))
    :local-ci? true :configure configure-staged
    :configuration-change #(update-in % [:frontend-configuration :install-options] (fn [options] (into {} options)))))

(def module-a (publication/str-name "EmptyGraphA"))
(def module-b (publication/str-name "GraphB"))
(def answer-a (publication/str-name "answer"))
(def answer-b (publication/str-name "b"))
(defn boxed [name] ["str" name "_boxed"])
(defn request-for [module]
  (assoc source/init-request :module module))
(defn imports-for [parents]
  (into source/init-requests (map request-for parents)))
(defn fixture-rows []
  (mapv #(json/read-str % :key-fn keyword)
        (str/split-lines (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl"))))
(defn b-bundle-rows []
  (let [rows (fixture-rows) manifest (first rows)
        primary (first (filter #(= answer-a (:name %)) (rest rows)))
        adapter (first (filter #(= (boxed answer-a) (:name %)) (rest rows)))
        b (-> primary (assoc :name answer-b :sourceModule module-b :sourceLocal true
                            :dependencies [answer-a])
              (assoc-in [:ir :fdecl :f] answer-b)
              (assoc-in [:ir :fdecl :body]
                ["vdecl" {:idx 3} "tobject"
                 {:fap {:c answer-a :ys [{:var {:id {:idx 1}}} {:var {:id {:idx 2}}}]}}
                 ["ret" {:var {:id {:idx 3}}}]]))
        b-boxed (-> (walk/postwalk #(if (= answer-a %) answer-b %) adapter)
                    (assoc :sourceModule module-b :sourceLocal true))
        manifest (-> manifest (assoc :requestedRoots [answer-b]
                                    :entryPoints [{:name answer-b :boxedTarget (boxed answer-b)}])
                     (assoc-in [:initializationPlan :module] module-b)
                     (assoc-in [:initializationPlan :imports]
                       (mapv #(hash-map :module (:module %) :meta (:isMeta %)) (imports-for [module-a]))))]
    (into [manifest b b-boxed]
          (map #(assoc % :sourceModule module-a :sourceLocal false) (rest rows)))))
(defn independent-b-bundle-rows
  "Explicit independent identity-function compiler fixture for native-base tests."
  []
  (let [rows (walk/postwalk #(if (= answer-a %) answer-b %) (fixture-rows))]
    (into [(-> (first rows) (assoc-in [:initializationPlan :module] module-b)
               (assoc-in [:initializationPlan :imports]
                 (mapv #(hash-map :module (:module %) :meta (:isMeta %)) source/init-requests)))]
          (map #(assoc % :sourceModule module-b :sourceLocal true) (rest rows)))))

(defn fixture-witness [name rows]
  (json/write-str {:schema "lean-eval-const-witness/1" :producer "RuntimeCompileShim.exportEvalConstWitness"
                  :leanCommit (get prim/pinned-build "lean_get_githash")
                  :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                  :name name :boxedTarget (boxed name) :sorryDep nil :missingDependencies [] :declarations rows}))

(defn configure-chain [input]
  (let [{:keys [functions bindings state] :as configured} (configure-staged input)
        witness (publication/str-name "GraphFixtureWitness")
        publish (publication/str-name "GraphKernelPublishDefinition")
        empty (publication/str-name "GraphKernelEmpty")
        error (publication/str-name "GraphKernelError")
        kernel-probe (publication/str-name "GraphKernelAddProbe")
        a-rows (mapv #(assoc % :sourceModule module-a :sourceLocal false) (rest (fixture-rows)))
        witnesses {answer-a (fixture-witness answer-a a-rows)
                   answer-b (fixture-witness answer-b (mapv #(assoc % :sourceLocal false)
                                                            (rest (if (:independent-b? input)
                                                                    (independent-b-bundle-rows) (b-bundle-rows)))))}
        specs
        {witness [3 [{:ty "object" :borrow false} {:ty "object" :borrow false} {:ty "object" :borrow false}]
                  (fn [_ world [environment name _]]
                    (let [target (wire-name (bridge/project-name-bounded world name {:max-nodes 64 :max-chars 512}))
                          text (or (get witnesses target) (throw (ex-info "Unknown fixed chain witness root" {})))
                          world (-> world (m/release environment 1) (m/release name 1))]
                      (m/allocate world :ctor 0 [text])))]
         empty [1 [{:ty "object" :borrow true}] (fn [_ world _] [world 0])]
         error [1 [{:ty "object" :borrow true}]
                (fn [_ world [message]]
                  (let [[world error] (m/allocate world :ctor 0 [message])]
                    (m/allocate world :ctor 0 [error])))]
         publish [2 [{:ty "object" :borrow false} {:ty "object" :borrow true}]
                  (fn [_ world [environment declaration]]
                    ;; This models ONLY post-check guest publication. The
                    ;; production kernel-host binding does the real admission.
                    (let [root (first (fields world environment))
                          values (fields world (first (fields world root)))
                          [world values] (copy-array! world (conj (vec values) declaration))
                          [world root] (m/allocate world :ctor 0 [values])
                          ;; Copy the immutable model envelope payload from the
                          ;; actual current parent Environment, never an ID cache.
                          _ (model-environment-metadata world environment)
                          [world next] (m/allocate world :ctor 0 [root (second (fields world environment))])
                          world (m/release world environment 1)]
                      (m/allocate world :ctor 1 [next])))]}
        bindings (reduce-kv
                   (fn [out target [_ params handler]]
                     (assoc out (str "graph_chain_model_" (pr-str target))
                            {:signature {:params params :return-type (if (= target empty) "uint8" "object")}
                             :handler handler})) bindings specs)
        functions (reduce-kv
                    (fn [out target [arity _ _]]
                      (let [symbol (str "graph_chain_model_" (pr-str target)) params (vec (range 1 (inc arity))) result (inc arity)]
                        (assoc out target {:params params :raw-extern {:symbol symbol :signature (:signature (get bindings symbol))}
                                           :body [:host symbol (mapv #(vector :var %) params) result [:return [:var result]]]})))
                    functions specs)
        helpers {:root (:root imports/helpers) :constant-map (:constant-map imports/helpers)
                 :quot-init? (:quot-init? imports/helpers) :empty? empty
                 :definition publish :definition-any publish :axiom publish :error error}
        kernel-binding (kernel-host/make-binding helpers {:allow-unsafe? true})
        bindings (assoc bindings "lean_elab_add_decl" kernel-binding)
        functions (assoc functions kernel-probe {:params [1 2 3 4 5]
                         :body [:host "lean_elab_add_decl" [[:var 1] [:var 2] [:var 3] [:var 4] [:var 5]] 6
                                [:return [:var 6]]]})]
    (assoc configured :functions functions :bindings bindings :kernel-probe kernel-probe
                      :independent-b? (true? (:independent-b? input)))))

(defn chain-invoke! [fixture active world target args]
  (try
    (let [called (raw/call @active world target args)]
      (remember! (get-in fixture [:transport :state]) :chain-raw called)
      (reset! active (:session called)) [(:state called) (:value called)])
    (catch Throwable cause
      (remember! (get-in fixture [:transport :state]) :chain-raw-failure cause)
      (throw cause))))
(defn chain-compile-model
  "Modeled source/export orchestration. B uses real kernel-host admission and
   real frontend decoding/installation; C is a distinct initializer-free empty
   unit. Every parent Java projection comes from the actual current checked base."
  [fixture context request _]
  (swap! (:compiler-calls fixture) inc)
  (let [entry (resident/snapshot context) module (wire-name (:module-name request))
        b? (= module-b module) parent (if b? module-a module-b)
        independent? (and b? (true? (get-in fixture [:transport :independent-b?])))
        requested (if independent? source/init-requests (imports-for [parent])) active (atom (:session entry))
        invoke #(chain-invoke! fixture active %1 %2 %3)
        names [(Name/fromString (if b? "b" "unusedC")) (Name/fromString (if b? "b._boxed" "unusedC._boxed"))
               (Name/fromString "Init") (Name/fromString (imports/module-string parent)) (:module-name request)]
        [world encoded] (encoding/encode-names (:world entry) invoke names)
        refs (fields world encoded)
        world (-> (reduce #(m/retain %1 %2 1) world refs) (m/release encoded 1))
        [own-name own-extra init-name parent-name module-name] refs
        [world own-ci environment]
        (if b?
          (let [a (get-in world [:source-modules module-a :data])
                a-ci (first (fields world (nth (fields world a) 2)))
                a-definition (first (fields world a-ci))
                a-base (first (fields world a-definition))
                type-ref (nth (fields world a-base) 2)
                answer-name (first (fields world a-base))
                target ["str" ["str" ["str" ["anonymous"] "Lean"] "Expr"] "const"]
                [world value] (if independent?
                                (let [value (second (fields world a-definition))] [(m/retain world value 1) value])
                                (invoke (m/retain world answer-name 1) ["str" target "_override"] [answer-name (m/->Tag 0)]))
                world (-> world (m/retain own-name 2) (m/retain type-ref 1))
                [world base] (record/ctor world 0 [own-name (m/->Tag 0) type-ref] 0)
                [world all] (record/ctor world 1 [own-name (m/->Tag 0)] 0)
                [world definition] (record/ctor world 0 [base value (m/->Tag 0) all] 1)
                world (record/scalar! world definition 0 "uint8" 1)
                [world declaration] (record/ctor world 1 [definition] 0)
                a-java (imported/project-constant world a-ci)
                expected (kernel-env/mk-def (Name/fromString "b") [] (.type ^ansatz.kernel.ConstantInfo a-java)
                                           (if independent? (.value ^ansatz.kernel.ConstantInfo a-java)
                                             (expression/const' (Name/fromString "answer") [])))
                _ (when-not (= (imported/checking-shape expected)
                               (imported/checking-shape (imported/project-constant world declaration)))
                    (throw (ex-info "Chain B guest declaration differs from independent Java definition" {})))
                [world result] (invoke (m/retain world (:environment entry) 1)
                                      (get-in fixture [:transport :kernel-probe])
                                      [(:environment entry) 1000000 1000 declaration (m/->Tag 0)])
                node (m/node world result)
                _ (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0))
                    (throw (ex-info "Actual kernel host did not admit chain B declaration" {})))
                environment (first (:fields node))
                world (-> world (m/retain environment 1) (m/release result 1) (assoc :result 0))]
            (remember! (get-in fixture [:transport :state]) :B-kernel-owned {:world world :environment environment :declaration declaration})
            [world declaration environment])
          [(-> world (m/release own-name 1) (m/release own-extra 1)) nil (:environment entry)])
        rows (if b? (if independent? (independent-b-bundle-rows) (b-bundle-rows))
               [(-> (first (fixture-rows)) (assoc :entryPoints [] :requestedRoots [])
                    (assoc-in [:initializationPlan :module] module)
                    (assoc-in [:initializationPlan :imports]
                      (mapv #(hash-map :module (:module %) :meta (:isMeta %)) requested)))])
        bundle (str/join "\n" (map json/write-str rows))
        compiled
        (if b?
          (let [[world roots] (array! (m/retain world own-name 1) [own-name])
                envelope {:schema "lean-file-compilation/1" :producer "RuntimeCompileShim.compileImportedFileState"
                          :leanCommit (get prim/pinned-build "lean_get_githash")
                          :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                          :fileName (:file-name request) :mainModule module :moduleSystem false
                          :requestedImports requested :success true :stage "complete" :environmentState "after-commands"
                          :diagnostics [] :bundle bundle}
                [world pair] (m/allocate world :ctor 0 [environment (json/write-str envelope)])
                [world io] (m/allocate world :ctor 0 [pair])
                result {:state (assoc world :status :done :result io) :value io :session @active}
                _ (remember! (get-in fixture [:transport :state]) :modeled-nonempty-B-compiler-IO result)
                compiled (frontend/finish-compilation-refs result {:file-name (:file-name request) :roots roots}
                                                          (:frontend-configuration (:configuration fixture)))
                _ (remember! (get-in fixture [:transport :state]) :actual-nonempty-B-installed compiled)]
            (reset! active (:session compiled))
            (update compiled :world m/release roots 1))
          (let [installed (eval/install-bundle world bundle {})]
            {:world (:world installed) :environment environment :success true
             :handle {:module-name module :unit-digest (:unit-digest installed)}
             :envelope {:success true :stage "complete" :mainModule module :moduleSystem false :requestedImports requested}}))
        world (:world compiled)
        exporter
        (fn [world target args]
          (if (= target (:root imports/helpers))
            (let [root (first (fields world (first args)))] [(m/retain world root 1) root])
            (let [[world r0] (packed! (m/retain world init-name 1) [init-name] 3 {0 0 1 1 2 0})
                  [world r1] (packed! world [init-name] 3 {0 0 1 1 2 1})
                  [world rp] (if independent? [(m/release world parent-name 1) nil]
                               (packed! world [parent-name] 3 {0 0 1 1 2 0}))
                  [world requests] (array! world (if independent? [r0 r1] [r0 r1 rp]))
                  [world own-names] (array! world (if b? [own-name] []))
                  [world constants] (array! world (if b? [own-ci] []))
                  [world extras] (array! world (if b? [own-extra] []))
                  [world extensions] (array! world [])
                  [world data] (packed! world [requests own-names constants extras extensions] 1 {0 0})
                  metadata (assoc module-model/metadata :module module :imports requested
                                  :constantNames (if b? [answer-b] []) :constantCount (if b? 1 0)
                                  :extraConstantNames (if b? [(boxed answer-b)] []) :extensions [])
                  world (-> world (m/release (first args) 1) (m/release (second args) 1))
                  [world pair] (m/allocate world :ctor 0 [data (json/write-str metadata)])]
              (m/allocate world :ctor 0 [pair]))))
        registered (source/register-compiled-graph world exporter compiled module-name requested)
        world (cond-> (m/release (:world registered) module-name 1)
                b? (m/release (:environment entry) 1))
        prepared (assoc entry :world world :environment (:environment compiled) :session @active)
        result-context (resident/adopt-prepared prepared (:configuration fixture))
        _ (remember! (get-in fixture [:transport :state]) :chain-publication-context result-context)
        digest (get-in compiled [:handle :unit-digest])
        unit (get-in world [:eval-const-authorizations :units digest])]
    {:context result-context :success true :file (resident/->FileHandle digest unit (:module-name request))
     :publication {:profile :graph}}))

(defn graph-request [module parents roots]
  {:text (str (str/join "\n" (map #(str "import " (imports/module-string %)) parents)) "\n")
   :file-name (str (imports/module-string module) ".lean")
   :module-name (Name/fromString (imports/module-string module))
   :roots (mapv #(Name/fromString (imports/module-string %)) roots) :initialization :defer})

(defn publish-child! [fixture context module parents parent-modules roots]
  (swap! (get-in fixture [:transport :state]) update :headers conj (imports-for parent-modules))
  (with-redefs [prototype.resident-source/load-and-publish-graph (partial chain-compile-model fixture)]
    (let [published (graph/publish-source-graph-node context (graph-request module parent-modules roots)
                      (:prefix fixture) (:profile fixture) parents
                      {:proof-budgets (select-keys budgets [:helper-fuel :attempt-fuel])})]
      (swap! (:captured fixture) conj (:context published))
      (remember! (get-in fixture [:transport :state]) :published-child published))))

(defn prepare-roots! [fixture context caps modules]
  (swap! (get-in fixture [:transport :state]) update :headers conj (imports-for modules))
  (graph/prepare-source-graph-import context
    (graph-request (publication/str-name "ChainConsumer") modules [])
    (:prefix fixture) (:profile fixture) caps {:kernel-policy policy :budgets budgets}))

(defn import-roots! [fixture context caps modules]
  (remember! (get-in fixture [:transport :state]) :chain-import-start {:modules modules :context context})
  (try
  (let [prepared (prepare-roots! fixture context caps modules)
        _ (complete-io! (:control prepared))
        result (graph/finish-source-graph-import! (:control prepared))]
    (remember! (get-in fixture [:transport :state]) :completed-chain result)
    (swap! (:captured fixture) conj (:context result)) result)
  (catch Throwable cause
    (remember! (get-in fixture [:transport :state]) :failed-chain-import {:modules modules :cause cause})
    (throw (ex-info (str "Chain import failed for " (imports/module-string (first modules))) {} cause)))))

(defn graph-eval-answer! [fixture context cap name]
  (let [packet (resident/snapshot context)
        data (#'graph/graph-node! cap)
        called (raw/call (:session packet) (:world packet) (get-in fixture [:transport :probe])
                        [m/erased (:environment packet) (:options packet) (get-in data [:wire-names name])])
        _ (remember! (get-in fixture [:transport :state]) :chain-public-eval called)
        wrapper (m/node (:state called) (:value called))
        _ (when-not (and (= 1 (:tag wrapper)) (bridge/constructor-layout? wrapper 1 0))
            (throw (ex-info "Chain public eval did not return owned Except.ok" {})))
        closure (first (:fields wrapper))
        world (-> (:state called) (m/retain closure 1) (m/release (:value called) 1) (assoc :result 0))
        _ (remember! (get-in fixture [:transport :state]) :chain-eval-cleaned
                     {:world world :session (:session called) :closure closure})
        answer (raw/call (:session called) world (get-in fixture [:transport :apply-probe]) [closure 41])]
    (remember! (get-in fixture [:transport :state]) :chain-public-answer answer)))

(defn receipt-in [packet module]
  (#'graph/graph-receipt! (get-in packet [:world :source-modules module :graph-import])))

(defn reaches-identical?
  "Identity reachability over the graph ledger only; stop at intentional opaque
   node/code/native authority roots. Never traverse or claim removal of the
   independent kernel anchor history in a complete World."
  [root target stops]
  (let [seen (java.util.IdentityHashMap.)]
    (loop [todo [root] remaining 20000]
      (when (zero? remaining) (throw (ex-info "Graph ledger identity walk exceeded fixture bound" {})))
      (if (seq todo)
        (let [value (peek todo)]
        (cond (identical? target value) true
              (or (some #(identical? % value) stops) (.containsKey seen value))
              (recur (pop todo) (dec remaining))
              :else (do (.put seen value true)
                        (recur (into (pop todo) (cond (map? value) (mapcat identity value)
                                                      (coll? value) value :else []))
                               (dec remaining)))))
        false))))

(deftest receipt-reachability-walk-does-not-stop-at-false-or-nil
  (let [target (Object.)]
    (is (true? (reaches-identical? [target false] target [])))
    (is (true? (reaches-identical? [target nil] target [])))
    (is (false? (reaches-identical? [nil false] target [])))))

(deftest nonempty-B-uses-checked-A-through-real-kernel-and-file-installer
  ;; Compiler serialization/finalizer/header are models. Declaration admission,
  ;; decoder/installer, G1 assembler, whole-union Java checks and graph authority
  ;; are the actual production paths; this is not genuine Lean frontend output.
  (doseq [backend [:reference :mutable :jvm]]
    (publication/with-empty-publication backend
      (fn [{:keys [transport captured] :as fixture}]
        (let [a (publish! fixture) _ (swap! captured conj (:context a))
              first-a (import-roots! fixture (:context a) [(:graph-node a)] [module-a])
              old-packet (resident/snapshot (:context first-a))
              b (publish-child! fixture (:context first-a) module-b [(:graph-node a)] [module-a] [answer-b])
              b-packet (resident/snapshot (:context b))
              before-b (failure #(graph-eval-answer! fixture (:context b) (:graph-node b) answer-b))
              _ (remember! (:state transport) :B-before-import-denial before-b)
              completed-b (import-roots! fixture (:context b) [(:graph-node b)] [module-b])
              packet-b (resident/snapshot (:context completed-b))
              receipt-a (receipt-in packet-b module-a) receipt-b (receipt-in packet-b module-b)
              module-c (publication/str-name "GraphC")
              c (publish-child! fixture (:context completed-b) module-c [(:graph-node b)] [module-b] [])
              completed-c (import-roots! fixture (:context c) [(:graph-node c)] [module-c])
              packet-c (resident/snapshot (:context completed-c))
              called-a (graph-eval-answer! fixture (:context completed-c) (:graph-node a) answer-a)
              called-b (graph-eval-answer! fixture (:context completed-c) (:graph-node b) answer-b)
              repeat-c (import-roots! fixture (:context completed-c) [(:graph-node c)] [module-c])
              repeated (resident/snapshot (:context repeat-c))
              old-called (graph-eval-answer! fixture (:context first-a) (:graph-node a) answer-a)
              retained-b-called (graph-eval-answer! fixture (:context completed-c) (:graph-node b) answer-b)
              new-called (graph-eval-answer! fixture (:context repeat-c) (:graph-node b) answer-b)
              new-a (receipt-in repeated module-a) new-b (receipt-in repeated module-b)
              old-a (receipt-in packet-c module-a) old-b (receipt-in packet-c module-b)]
          (is (some? before-b))
          (is (= "Source import lacks checked module installation authority" (.getMessage ^Throwable before-b)))
          (is (= 1 (count (:projected receipt-a))))
          (is (true? (identical? (:checked-env receipt-a) (:checked-env receipt-b))))
          (is (= [(publication/str-name "Init") module-a module-b] (:module-order receipt-b)))
          (is (= 1 (:module-index receipt-a))) (is (= 2 (:module-index receipt-b)))
          (is (= 3 (count (:graph-import-receipts completed-c))))
          (is (= [(publication/str-name "Init") module-a module-b module-c] (:module-order (receipt-in packet-c module-c))))
          (is (= 41 (:value called-a))) (is (= 41 (:value called-b)))
          (is (= 41 (:value old-called))) (is (= 41 (:value retained-b-called))) (is (= 41 (:value new-called)))
          (is (false? (identical? (get-in old-a [:projected (Name/fromString "answer")])
                                  (get-in new-a [:projected (Name/fromString "answer")]))))
          (is (false? (identical? (get-in old-b [:projected (Name/fromString "b")])
                                  (get-in new-b [:projected (Name/fromString "b")]))))
          (is (true? (identical? old-packet (resident/snapshot (:context first-a)))))
          (doseq [[module old] [[module-a old-a] [module-b old-b]]]
            (let [cap (get-in repeated [:world :source-modules module :graph-import])
                  current (#'graph/graph-receipt! cap)]
              (is (false? (reaches-identical? current old [(:node current) (:profile fixture) (:prefix fixture)])))))
          (let [description (model-environment-metadata (:world packet-c) (:environment packet-c))]
            (is (= 1 (get-in description [:indices (Name/fromString "answer")])))
            (is (= 1 (get-in description [:indices (Name/fromString "answer._boxed")])))
            (is (= 2 (get-in description [:indices (Name/fromString "b")])))
            (is (= 2 (get-in description [:indices (Name/fromString "b._boxed")]))))
          (is (= 3 (count (set (map #(get-in (resident/snapshot (:context %))
                                                [:world :source-modules %2 :unit-digest])
                                       [a b c] [module-a module-b module-c])))))))
      :local-ci? true :configure configure-chain)))

(deftest two-node-mid-batch-failure-keeps-first-registered-receipt-inactive
  (publication/with-empty-publication :reference
    (fn [{:keys [transport captured configuration compiler-calls prefix profile] :as fixture}]
      (let [a (publish! fixture) _ (swap! captured conj (:context a))
            completed-a (import-roots! fixture (:context a) [(:graph-node a)] [module-a])
            b (publish-child! fixture (:context completed-a) module-b [(:graph-node a)] [module-a] [answer-b])
            old (resident/snapshot (:context b))
            prepared (prepare-roots! fixture (:context b) [(:graph-node b)] [module-b])
            control (:control prepared) _ (complete-io! control)
            registry @#'graph/graph-receipts inserted (atom [])
            selected (ex-info "selected second graph receipt insertion failure" {})
            proxy-registry (proxy [java.util.WeakHashMap] []
                             (get [key] (.get ^java.util.WeakHashMap registry key))
                             (put [key value]
                               (when (= 1 (count @inserted)) (throw selected))
                               (let [previous (.put ^java.util.WeakHashMap registry key value)]
                                 (swap! inserted conj key) previous)))]
        (with-redefs-fn {#'graph/graph-receipts proxy-registry}
          (fn []
            (let [cause (failure #(graph/finish-source-graph-import! control))
                  state (:source-graph-import-state (ex-data cause))
                  _ (remember! (:state transport) :mid-batch-failed-state {:cause cause :state state})
                  candidate (get-in state [:source-graph :batch-candidate-world])
                  batch (get-in state [:source-graph :candidate-batch])
                  finished (get-in state [:source-graph :checked-candidate])
                  packet (assoc (:entry state) :world candidate :session (:session state)
                                :environment (:environment finished))
                  ;; Deliberately use the exposed checked diagnostic World via
                  ;; public adoption. Registration alone must confer NO authority.
                  diagnostic-context (resident/adopt-prepared packet configuration)
                  _ (remember! (:state transport) :mid-batch-diagnostic-context diagnostic-context)
                  getter-before (count @(:operations fixture))
                  denied-a (failure #(graph-eval-answer! fixture diagnostic-context (:graph-node a) answer-a))
                  denied-b (failure #(graph-eval-answer! fixture diagnostic-context (:graph-node b) answer-b))
                  getter-after (count @(:operations fixture))
                  compiles-before @compiler-calls
                  _ (swap! (:state transport) update :headers conj (imports-for [module-b]))
                  parent-denied
                  (with-redefs [prototype.resident-source/load-and-publish-graph (partial chain-compile-model fixture)]
                    (failure #(graph/publish-source-graph-node diagnostic-context
                                (graph-request (publication/str-name "GraphFailedChild") [module-b] [])
                                prefix profile [(:graph-node b)]
                                {:proof-budgets (select-keys budgets [:helper-fuel :attempt-fuel])})))]
              (remember! (:state transport) :mid-batch-public-denials
                         {:A denied-a :B denied-b :parent parent-denied})
              (is (true? (identical? selected (.getCause ^Throwable cause))))
              (is (= 1 (count @inserted))) (is (= 2 (count batch)))
              (is (true? (identical? (first @inserted) (:cap (first batch)))))
              (is (true? (identical? (:receipt (first batch)) (.get proxy-registry (first @inserted)))))
              (is (nil? (.get proxy-registry (:cap (second batch)))))
              (is (every? #(false? (.get ^java.util.concurrent.atomic.AtomicBoolean
                                         (get-in % [:receipt :activation]))) batch))
              (is (true? (identical? (get-in (first batch) [:receipt :activation])
                                     (get-in (second batch) [:receipt :activation]))))
              (doseq [denied [denied-a denied-b]]
                (is (some? denied))
                (is (= "Source import lacks checked module installation authority" (.getMessage ^Throwable denied))))
              (is (= getter-before getter-after))
              (is (= "Expected an issued completed source graph receipt" (.getMessage ^Throwable parent-denied)))
              (is (= compiles-before @compiler-calls))
              (is (true? (identical? old (resident/snapshot (:context b)))))
              (is (true? (identical? cause (failure #(graph/finish-source-graph-import! control)))))
              (is (true? (identical? (:world state) (:checkpoint (ex-data cause)))))
              (is (some? (get-in state [:source-graph :checked-candidate :certificate])))
              (swap! diagnostics conj {:fixture fixture :failure cause :context diagnostic-context}))))))
    :local-ci? true :configure configure-chain))

(defn checked-B-without-current-AB-receipt!
  "Use REAL kernel-host B admission after a real reimport of A. Model only a
   header-only Env view with the prior AB header; no Java Env/certificate/receipt
   is fabricated. This deliberately lacks a current completed AB receipt."
  [fixture completed-a completed-b]
  (let [packet (resident/snapshot (:context completed-a))
        old-b (resident/snapshot (:context completed-b))
        metadata (second (fields (:world old-b) (:environment old-b)))
        declaration (first (fields (:world packet)
                             (nth (fields (:world packet) (get-in packet [:world :source-modules module-b :data])) 2)))
        called (raw/call (:session packet) (m/retain (:world packet) (:environment packet) 1)
                        (get-in fixture [:transport :kernel-probe])
                        [(:environment packet) 1000000 1000 declaration (m/->Tag 0)])
        _ (remember! (get-in fixture [:transport :state]) :rechecked-B-without-import called)
        node (m/node (:state called) (:value called))
        _ (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0))
            (throw (ex-info "Real B readmission into A base failed" {})))
        checked-env (first (:fields node))
        world (-> (:state called) (m/retain checked-env 1) (m/release (:value called) 1) (assoc :result 0))
        _ (remember! (get-in fixture [:transport :state]) :readmitted-owned-Env
                     {:world world :session (:session called) :environment checked-env})
        root (first (fields world checked-env))
        [world view] (m/allocate (m/retain world root 1) :ctor 0 [root metadata])
        world (-> world (m/release checked-env 1) (m/release (:environment packet) 1))
        _ (remember! (get-in fixture [:transport :state]) :readmitted-header-view
                     {:world world :session (:session called) :environment view})
        context (resident/adopt-prepared (assoc packet :world world :session (:session called) :environment view)
                                        (:configuration fixture))]
    (remember! (get-in fixture [:transport :state]) :readmitted-context context)
    (swap! (:captured fixture) conj context) context))

(deftest public-issued-graph-authority-is-bound-to-current-base-and-world-lineage
  (publication/with-empty-publication :reference
    (fn [{:keys [context prefix profile configuration compiler-calls captured transport] :as fixture}]
      (let [a (publish! fixture) _ (swap! captured conj (:context a))
            first-a (import-roots! fixture (:context a) [(:graph-node a)] [module-a])
            b (publish-child! fixture (:context first-a) module-b [(:graph-node a)] [module-a] [answer-b])
            completed-b (import-roots! fixture (:context b) [(:graph-node b)] [module-b])
            saved-b (resident/snapshot (:context completed-b))
            switched-a (import-roots! fixture (:context completed-b) [(:graph-node a)] [module-a])
            without-receipt (checked-B-without-current-AB-receipt! fixture switched-a completed-b)
            before-compiles @compiler-calls
            denied-current (failure #(publish-child! fixture without-receipt (publication/str-name "GraphNeedsReceipt")
                                                     [(:graph-node b)] [module-b] []))
            _ (remember! (:state transport) :no-current-AB-receipt-denial denied-current)
            ;; Same text/module, distinct actual publication operation/version,
            ;; from the pristine retained prepublication World. No heap merge.
            _ (swap! (:state transport) update :headers conj source/init-requests)
            sibling-a (publish! fixture) _ (swap! captured conj (:context sibling-a))
            _ (swap! (:state transport) update :headers conj (imports-for [module-b module-a]))
            mixed (failure #(graph/prepare-source-graph-import (:context completed-b)
                              (graph-request (publication/str-name "MixedLineage") [module-b module-a] [])
                              prefix profile [(:graph-node b) (:graph-node sibling-a)]
                              {:kernel-policy policy :budgets budgets}))]
        (remember! (:state transport) :mixed-A-versions-denial mixed)
        (is (= "Source graph parent is not inherited from its current completed import"
               (.getMessage ^Throwable denied-current)))
        (is (= before-compiles (dec @compiler-calls))) ;; Only sibling A compiled.
        (is (= "Source graph candidate differs from its sealed publication" (.getMessage ^Throwable mixed)))
        (is (false? (identical? (:graph-node a) (:graph-node sibling-a))))
        (is (true? (identical? saved-b (resident/snapshot (:context completed-b)))))
        (is (= 41 (:value (graph-eval-answer! fixture (:context completed-b) (:graph-node b) answer-b))))
        (is (= 41 (:value (graph-eval-answer! fixture (:context first-a) (:graph-node a) answer-a))))
        (publication/with-empty-publication :reference
          (fn [{foreign-context :context foreign-prefix :prefix foreign-profile :profile
                foreign-source :source :as foreign}]
            (let [foreign-a (publish! foreign)
                  _ (swap! (:captured foreign) conj (:context foreign-a))
                  packet (resident/snapshot (:context first-a))
                  wrong-source (resident/adopt-prepared (assoc-in packet [:world :native-imports] [foreign-source]) configuration)
                  _ (remember! (:state transport) :wrong-Source-context wrong-source)
                  changed-bindings (assoc (get-in packet [:session :bindings]) "lean_eval_const" (:eval-binding foreign))
                  changed-configuration (assoc configuration :trusted-bindings changed-bindings)
                  changed-packet (assoc packet :session (raw/open-functions (get-in packet [:world :functions])
                                                       changed-bindings {:backend :reference :fuel 1000000}))
                  wrong-configuration (resident/adopt-prepared changed-packet changed-configuration)
                  _ (remember! (:state transport) :wrong-configuration-context wrong-configuration)
                  cases [[:descriptive-profile (:context first-a) prefix {:profile :graph} [(:graph-node a)]]
                         [:descriptive-node (:context first-a) prefix profile [(:graph-publication a)]]
                         [:descriptive-prefix (:context first-a) {:state :descriptive} profile [(:graph-node a)]]
                         [:issued-profile (:context first-a) prefix foreign-profile [(:graph-node a)]]
                         [:issued-prefix (:context first-a) foreign-prefix profile [(:graph-node a)]]
                         [:foreign-issued-node (:context first-a) prefix profile [(:graph-node foreign-a)]]
                         [:Source wrong-source prefix profile [(:graph-node a)]]
                         [:configuration wrong-configuration prefix profile [(:graph-node a)]]]]
              (doseq [[label candidate selected-prefix selected-profile roots] cases]
                (let [before (resident/snapshot candidate) getters (count @(:operations fixture))
                      compiles @compiler-calls
                      cause (failure #(graph/prepare-source-graph-import candidate
                                        (graph-request (publication/str-name "RejectedAuthority") [module-a] [])
                                        selected-prefix selected-profile roots {:kernel-policy policy :budgets budgets}))]
                  (remember! (:state transport) :public-authority-denial {:label label :cause cause})
                  (is (some? cause) (name label))
                  (is (= :entry (get-in (ex-data cause) [:source-graph-import-state :phase])) (name label))
                  (is (= getters (count @(:operations fixture))) (name label))
                  (is (= compiles @compiler-calls) (name label))
                  (is (true? (identical? before (resident/snapshot candidate))) (name label))))
              ;; These two borrowed-Source candidates must close while the
              ;; separately owning foreign fixture still keeps its Store open.
              (resident/close! wrong-source) (resident/close! wrong-configuration)))
          :local-ci? true :configure configure-chain)))
    :local-ci? true :configure configure-chain))
