(ns prototype.project-loader-integration-test
  "Actual public coordinator/graph/native/registration/FileHandle path with fixed
   pre-captured compiler/header/export/finalizer transport MODELS. No genuine Lean
   frontend execution, nonempty imported-row permission or full capture claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.project-loader :as loader]
            [prototype.project-loader-test :as protocol]
            [prototype.project-discovery-test :as files]
            [prototype.source-graph-runtime-test :as publication]
            [prototype.source-graph-staged-test :as staged]
            [prototype.native-init-base-test :as native]
            [prototype.source-module-test :as module-model]
            [prototype.source-module :as source-module]
            [prototype.source-import :as source]
            [prototype.frontend :as frontend]
            [prototype.frontend-test :as frontend-model]
            [prototype.runtime-prim :as prim]
            [prototype.machine :as m]
            [prototype.kernel-bridge :as bridge]
            [prototype.interop-codec :as codec]
            [prototype.guest-encoding :as encoding]
            [prototype.resident-frontend :as resident])
  (:import [ansatz.kernel Name]
           [java.nio.charset StandardCharsets]))

(def specs
  {"-- source A\n" {:module ["A"] :parents []}
   "import A\n-- source B\n" {:module ["B"] :parents [["A"]]}
   "-- independent source D\n" {:module ["D"] :parents []}
   "import «B»\nimport «D»\n" {:view? true :parents [["B"] ["D"]]}})
(defn requested [parents]
  (into source/init-requests (map #(assoc source/init-request :module (files/wire %)) parents)))
(defn profile [] {:target "x86_64-unknown-linux-gnu" :wordBits 64})
(defn utf8 [^String text] (alength (.getBytes text StandardCharsets/UTF_8)))
(defn fail [text] (throw (ex-info text {})))
(defn wire-name [world name]
  (staged/wire-name (bridge/project-name-bounded world name {:max-nodes 64 :max-chars 512})))
(defn keep-control [before after]
  ;; Nested encoder helpers document clearing :result. Restore exactly that
  ;; incoming control field when returning to an active parent raw host handler.
  (if (contains? before :result) (assoc after :result (:result before)) (dissoc after :result)))
(defn encode-name [context world name]
  (let [[next value] (encoding/encode-name world (:invoke context) name)]
    [(keep-control world next) value]))
(defn compile-key [module] ["project-loader-modeled-compilation" module])
(defn compile-record [world module]
  (let [text (get-in world [:globals (compile-key module) :value])]
    (when-not (and (string? text) (<= (count text) 4096)) (fail "No bounded compiler invocation record"))
    (let [record (json/read-str text :key-fn keyword)]
      (when-not (and (= 3 (count record)) (= module (:module record))
                     (string? (:text record)) (contains? specs (:text record))
                     (= module (files/wire (:module (get specs (:text record)))))
                     (= (requested (:parents (get specs (:text record)))) (:imports record)))
        (fail "Exporter compiler invocation record changed"))
      record)))
(defn empty-bundle [module imports]
  ;; Same producer envelope shape; compiler output bytes are explicitly modeled.
  ;; Distinct main modules must produce distinct admitted manifest-only units.
  (json/write-str
    (-> (first (staged/fixture-rows))
        (assoc :entryPoints [] :requestedRoots [])
        (assoc-in [:initializationPlan :module] module)
        (assoc-in [:initializationPlan :imports]
          (mapv #(hash-map :module (:module %) :meta (:isMeta %)) imports)))))
(defn model-function [symbol arity signature]
  (let [params (vec (range 1 (inc arity))) result (inc arity)]
    {:params params :raw-extern {:symbol symbol :signature signature}
     :body [:host symbol (mapv #(vector :var %) params) result [:return [:var result]]]}))
(defn header-effect-key? [key]
  (and (vector? key) (= 2 (count key)) (= "project-loader-header-effect" (first key))
       (integer? (second key)) (<= 1 (second key) 64)))
(defn append-header-effect [world]
  ;; Globals model immutable cache entries: NativeBase must preserve every
  ;; preexisting entry object. Allocate a fresh bounded witness, never rewrite.
  (let [globals (:globals world)
        _ (when (> (count globals) 4096) (fail "Fixture globals exceed scan bound"))
        n (inc (count (filter header-effect-key? (keys globals))))
        key ["project-loader-header-effect" n] value {:status :ready :value n}]
    (when (or (> n 64) (contains? globals key)) (fail "Fixture header effects exceed bound"))
    [(assoc-in world [:globals key] value) key value]))
(defn configure [input]
  (let [{:keys [functions bindings] :as base} (native/configure-native-stage input)
        calls (atom []) returned (atom {})
        header (fn [_ world [text filename erased :as arguments]]
                 (let [text (codec/decode world :string text) filename (codec/decode world :string filename)
                       spec (or (get specs text) (fail "Unexpected exact captured header text"))
                       envelope {:schema "lean-file-header/1" :producer "RuntimeCompileShim.inspectFileHeader"
                                 :leanCommit (get prim/pinned-build "lean_get_githash") :runtimeProfile (profile)
                                 :fileName filename :moduleSystem false :hasErrors false :headerEndByte (utf8 text)
                                 :diagnostics [] :requestedImports (requested (:parents spec))}
                       world (reduce #(m/release %1 %2 1) world arguments)
                       [world effect-key effect-entry] (append-header-effect world)
                       result (m/allocate world :ctor 0 [(json/write-str envelope)])]
                   (swap! calls conj {:event :header :text text :effect-key effect-key :effect-entry effect-entry})
                   (swap! returned assoc :header {:world (first result) :value (second result)}) result))
        compile (fn [_ world [environment text filename module roots options erased :as arguments]]
                  (let [text (codec/decode world :string text) filename (codec/decode world :string filename)
                        module (wire-name world module) spec (get specs text)
                        _ (when-not (and spec (not (:view? spec)) (= module (files/wire (:module spec)))
                                         (m/ref? roots) (= :array (:kind (m/node world roots)))
                                         (empty? (staged/fields world roots)) (m/ref? environment) (m/ref? options))
                            (fail "Compiler model received mismatched captured input/roots/environment"))
                        _ (m/node world environment) _ (m/node world options)
                        imports (requested (:parents spec))
                        envelope {:schema "lean-file-compilation/1" :producer "RuntimeCompileShim.compileImportedFileState"
                                  :leanCommit (get prim/pinned-build "lean_get_githash") :runtimeProfile (profile)
                                  :fileName filename :mainModule module :moduleSystem false :requestedImports imports
                                  :success true :stage "complete" :environmentState "after-commands" :diagnostics []
                                  :bundle (empty-bundle module imports)}
                        ;; Record is immutable branch-local guest-global TEXT,
                        ;; not a Ref-ID cache, current-module atom or permission.
                        world (assoc-in world [:globals (compile-key module)]
                                        {:status :ready :value (json/write-str {:module module :text text :imports imports})})
                        ;; Caller transferred retained copies of all six inputs.
                        ;; Own a separate returned Env, then consume each input.
                        world (m/retain world environment 1)
                        world (reduce #(m/release %1 %2 1) world arguments)
                        [world pair] (m/allocate world :ctor 0 [environment (json/write-str envelope)])
                        result (m/allocate world :ctor 0 [pair])]
                    (swap! calls conj {:event :compile :module module :text text :imports imports
                                       :environment environment :root (first (staged/fields (first result) environment))
                                       :environment-modules
                                       (if (= 1 (count (staged/fields world environment)))
                                         ["Init"]
                                         (:modules (staged/model-environment-metadata world environment)))})
                    (swap! returned assoc [:compiler module] {:world (first result) :value (second result)}) result))
        export (fn [context world [environment name erased]]
                 (let [module (wire-name world name) record (compile-record world module)
                       incoming-root (first (staged/fields world environment))
                       [world requests]
                       (reduce (fn [[world out] request]
                                 (let [jname (staged/model-index-name (:module request))
                                       [world n] (encode-name context world jname)
                                       [world r] (staged/packed! world [n] 3 {0 (if (:importAll request) 1 0)
                                                                             1 (if (:isExported request) 1 0)
                                                                             2 (if (:isMeta request) 1 0)})]
                                   [world (conj out r)])) [world []] (:imports record))
                       [world imports] (staged/array! world requests)
                       [world names] (staged/array! world []) [world constants] (staged/array! world [])
                       [world extras] (staged/array! world []) [world extensions] (staged/array! world [])
                       [world data] (staged/packed! world [imports names constants extras extensions] 1 {0 0})
                       metadata (assoc module-model/metadata :module module :imports (:imports record)
                                       :constantNames [] :constantCount 0 :extraConstantNames [] :extensions [])
                       world (reduce #(m/release %1 %2 1) world [environment name erased])
                       [world pair] (m/allocate world :ctor 0 [data (json/write-str metadata)])
                       result (m/allocate world :ctor 0 [pair])]
                   (swap! calls conj {:event :export :module module :imports (:imports record)
                                      :environment environment :root incoming-root})
                   (swap! returned assoc [:export module] {:world (first result) :value (second result)}) result))
        handlers {frontend/header-target [3 header] frontend/compile-target [7 compile] source-module/export-helper [3 export]}
        configured
        (reduce-kv
          (fn [out target [arity handler]]
            (let [old (get functions target)
                  expected-old
                  (cond
                    (= target frontend/header-target)
                    (model-function (str "graph_staged_model_" (pr-str target)) 3
                                    {:params (vec (repeat 3 {:ty "object" :borrow false})) :return-type "object"})
                    (= target frontend/compile-target)
                    {:params [1 2 3 4 5 6 7]
                     :body (frontend-model/drop-args [2 3 4 5 6]
                             [:let 8 [:ctor 0 [[:var 1] [:imm (json/write-str (frontend-model/envelope false))]]]
                              [:let 9 [:ctor 0 [[:var 8]]] [:return [:var 9]]]])}
                    (= target source-module/export-helper) {:params [] :body [:return [:imm 0]]}
                    :else nil)
                  _ (when-not (and expected-old (= old expected-old))
                      (fail (str "Integration setup differs from exact known transport model at "
                                 (cond (= target frontend/header-target) "header"
                                       (= target frontend/compile-target) "compiler"
                                       (= target source-module/export-helper) "export"
                                       :else "unknown"))))
                  symbol (str "project_loader_fixed_model_" (pr-str target))
                  ;; TEST HOST-SHIM ABI, not an assertion about lowered Lean
                  ;; fdecl ABI. frontend/compile-file-refs transfers six retained
                  ;; input owners + erased; source-module/export-classic transfers
                  ;; retained Env/Name + erased; header owns text/file + erased.
                  signature {:params (vec (repeat arity {:ty "object" :borrow false})) :return-type "object"}]
              (-> out (assoc-in [:bindings symbol] {:signature signature :handler handler})
                  (assoc-in [:functions target] (model-function symbol arity signature))))) base handlers)]
    (assoc configured :project-calls calls :project-returned returned)))

(defn empty-export-records []
  (mapv #(hash-map :module (files/wire [%]) :roots []) ["A" "B" "D"]))
(def diagnostics (atom nil))
(deftest actual-empty-node-parent-and-independent-leaf-coordination
  (doseq [backend [:reference :mutable :jvm]]
    (files/with-files {["A"] "-- source A\n" ["B"] "import A\n-- source B\n" ["D"] "-- independent source D\n"}
      (fn [_ provider]
        (publication/with-empty-publication backend
          (fn [{:keys [transport] :as fixture}]
            (let [owned (atom [])]
              (try
                (let [token (native/modeled-stage-token fixture)
                      ready (native/modeled-guards-context fixture (:context fixture) native/complete-guards)
                      before (resident/snapshot ready)
                      policies {:discovery-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                                :publication-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                                :import-options {:kernel-policy staged/policy :budgets staged/budgets}
                                :native-options {:kernel-policy staged/policy :budgets staged/budgets}}
                      project (loader/open-project ready (assoc (protocol/options fixture provider)
                                                          :native-readiness token :policies policies))
                      _ (swap! owned conj project)
                      prepared (loader/prepare-load project {:roots [(files/wire ["B"]) (files/wire ["D"])]
                                                             :exports (empty-export-records)})
                      result (protocol/complete! (:control prepared))
                      version (:project result) _ (swap! owned conj version)
                      data (#'loader/version! version) packet (resident/snapshot (:context data))
                      entries (mapv #(get-in packet [:world :source-modules (files/wire [%])]) ["A" "B" "D"])
                      calls @(:project-calls transport)
                      compiled (filter #(= :compile (:event %)) calls)
                      receipts (mapv #(staged/receipt-in packet (files/wire [%])) ["A" "B" "D"])
                      files (mapv #(get-in result [:files [%]]) ["A" "B" "D"])]
                  (is (= [["A"] ["B"] ["D"]] (get-in result [:modules :order])))
                  (is (= (mapv #(files/wire [%]) ["A" "B" "D"]) (mapv :module compiled)))
                  (is (= ["-- source A\n" "import A\n-- source B\n" "-- independent source D\n"] (mapv :text compiled)))
                  (is (= 3 (count (filter #(= :export (:event %)) calls))))
                  ;; Actual parent import precedes B; the independent D compile
                  ;; receives the native-only reset, rather than B's projection.
                  (is (= [["Init"] ["Init" "A"] ["Init"]] (mapv :environment-modules compiled)))
                  (is (= [["B"] ["D"]] (get-in result [:modules :roots])))
                  (let [description (staged/model-environment-metadata (:world packet) (:environment packet))]
                    (is (= ["Init" "A" "B" "D"] (:modules description)))
                    (is (= (requested [["B"] ["D"]]) (:requests description))))
                  (let [headers (filter #(= :header (:event %)) calls)
                        header-effect-keys (filter header-effect-key? (keys (get-in packet [:world :globals])))]
                    (is (pos? (count headers)))
                    (is (= (count headers) (count header-effect-keys)))
                    (is (empty? (filter header-effect-key? (keys (get-in before [:world :globals])))))
                    (is (every? (fn [{:keys [effect-key effect-entry]}]
                                  (identical? effect-entry (get-in packet [:world :globals effect-key]))) headers)))
                  (doseq [module ["A" "B" "D"]]
                    (is (= (files/wire [module]) (:module (compile-record (:world packet) (files/wire [module]))))))
                  ;; FileHandle originates from the actual resident-source public
                  ;; path. This fixture never calls its constructor or redefines
                  ;; registration/adoption/publication/receipt operations.
                  (is (every? #(instance? prototype.resident_frontend.FileHandle %) files))
                  (is (= 3 (count (set (map #(.-digest ^prototype.resident_frontend.FileHandle %) files)))))
                  (is (<= (count @(:project-returned transport)) 7))
                  (doseq [[entry file receipt module] (map vector entries files receipts ["A" "B" "D"])]
                    (let [wire (files/wire [module])
                          compile (first (filter #(and (= :compile (:event %)) (= wire (:module %))) calls))
                          export (first (filter #(and (= :export (:event %)) (= wire (:module %))) calls))]
                      ;; These Ref observations prove forwarding in this branch;
                      ;; they are never consulted for metadata/authority lookup.
                      (is (= (:environment compile) (:environment export) (:environment entry)))
                      (is (= (:root compile) (:root export)
                             (first (staged/fields (:world packet) (:environment entry)))))
                      (is (some? (get @(:project-returned transport) [:compiler wire])))
                      (is (some? (get @(:project-returned transport) [:export wire]))))
                    (is (= :graph (:profile entry)))
                    (is (= (files/wire [module]) (get-in entry [:unit :manifest :initializationPlan :module])))
                    (is (= [] (get-in entry [:unit :declarations])))
                    (is (= [] (get-in entry [:unit :actions])))
                    (is (true? (identical? (:unit entry) (.-unit ^prototype.resident_frontend.FileHandle file))))
                    (is (true? (identical? (:checked-env (first receipts)) (:checked-env receipt))))
                    (is (= [source/init-module (files/wire ["A"]) (files/wire ["B"]) (files/wire ["D"])]
                           (:module-order receipt))))
                  (is (true? (identical? before (resident/snapshot ready))))
                  (is (nil? (seq (get-in before [:world :source-modules]))))
                  (is (= 3 (count (:nodes data))))
                  (is (every? #(instance? prototype.resident_init_prefix.SourceGraphNode %) (vals (:nodes data))))
                  (is (= :finished (get-in result [:progress :phase])))
                  (doseq [project (reverse @owned)] (loader/close-project! project))
                  (reset! owned []))
                (catch Throwable cause
                  (compare-and-set! diagnostics nil {:cause cause :projects @owned :backend backend})
                  (throw cause)))))
          :configure configure)))))
