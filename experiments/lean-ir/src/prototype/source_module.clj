(ns prototype.source-module
  "Owned classic source ModuleData export. This is not a native transport,
   initialization receipt, kernel certificate, or published-module registry."
  (:refer-clojure :exclude [byte])
  (:require [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.kernel-bridge :as bridge]
            [prototype.runtime-string :as string]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-abi :as abi])
  (:import [ansatz.kernel Name]))

(def export-helper
  ["str" ["str" ["str" ["anonymous"] "SourceModuleExport"] "exportClassic"] "_boxed"])

(def ir-export-targets
  ;; Exact @[export] targets in the pinned Compiler/IR/CompilerM.lean.
  (into {}
    (for [[symbol leaf] [["lean_ir_export_entries" "exportIREntries"]
                         ["lean_get_ir_extra_const_names" "getIRExtraConstNames"]]]
      [symbol (reduce (fn [prefix segment]
                        (if (integer? segment) ["num" prefix (str segment)]
                          ["str" prefix segment]))
                      ["anonymous"] ["_private" "Lean" "Compiler" "IR" "CompilerM" 0 "Lean" "IR" leaf])])))

(defn with-ir-export-aliases
  "Add only the two pinned aliases needed for ModuleData/IR export. Existing
   alias conflicts, missing guest bodies, and exact parameter/ownership/return
   ABI mismatches remain hard errors in runtime-abi's deferred lowerer."
  [catalogue]
  (abi/with-export-aliases catalogue
    {:declarations {}
     :manifests [{:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
                  :leanCommit (get prim/pinned-build "lean_get_githash")
                  :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                  :exports (mapv (fn [[symbol name]] {:symbol symbol :name name}) ir-export-targets)}]}))

(defn- fail [message data] (throw (ex-info message data)))
(defn- structured-name [^Name name]
  (loop [name name segments []]
    (case (.tag name)
      0 (reduce (fn [prefix [kind value]] [kind prefix value]) ["anonymous"] (rseq segments))
      1 (recur (.prefix name) (conj segments ["str" (.str name)]))
      2 (recur (.prefix name) (conj segments ["num" (str (.num name))])))))
(defn- name-value [world value] (structured-name (bridge/project-name world value)))
(defn- ctor [world value fields scalar-size]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= 0 (:tag node)) (bridge/constructor-layout? node fields scalar-size))
      (fail "Malformed source module export constructor" {:value value})) node))
(defn- array [world value]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (= :array (:kind node)) (fail "Malformed source module export array" {:value value}))
    (:fields node)))
(defn- byte [node offset]
  (m/read-scalar-node node {:index (count (:fields node)) :offset offset :type "uint8" :region :scalar}))
(defn- import-value [world value]
  (let [node (ctor world value 1 3)
        flags (mapv #(byte node %) (range 3))]
    (when-not (every? #{0 1} flags) (fail "Invalid source module import flags" {}))
    (zipmap [:module :importAll :isExported :isMeta]
      (into [(name-value world (first (:fields node)))] (mapv #(= 1 %) flags)))))

(defn- validate-metadata [world expected data text]
  (let [metadata (json/read-str text :key-fn keyword)
        node (ctor world data 5 1)
        [imports names constants extras entries] (:fields node)
        imports (mapv #(import-value world %) (array world imports))
        names (mapv #(name-value world %) (array world names))
        extras (mapv #(name-value world %) (array world extras))
        extensions (mapv (fn [entry]
                           (let [[name values] (:fields (ctor world entry 2 0))]
                             {:name (name-value world name) :entryCount (count (array world values))}))
                         (array world entries))]
    (when-not (and (= "lean-source-module/1" (:schema metadata))
                   (= "SourceModuleExport.exportClassic" (:producer metadata))
                   (= "4.33.1" (:leanVersion metadata))
                   (= (get prim/pinned-build "lean_get_githash") (:leanCommit metadata))
                   (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile metadata))
                   (= "owned-guest-module-data" (:origin metadata))
                   (= "private" (:level metadata))
                   (false? (:moduleSystem metadata)) (= 0 (byte node 0))
                   (false? (:initializersExecuted metadata)) (false? (:environmentSerialized metadata))
                   (not= ["anonymous"] expected) (= expected (:module metadata))
                   (= imports (:imports metadata)) (= names (:constantNames metadata))
                   (= (count names) (:constantCount metadata) (count (array world constants)))
                   (= extras (:extraConstantNames metadata)) (= extensions (:extensions metadata)))
      (fail "Source ModuleData metadata/profile mismatch" {:module expected}))
    metadata))

(defn export-classic
  "Borrow ENVIRONMENT and guest EXPECTED-MODULE Name. INVOKE is the scoped raw
   [world target args] -> [world owned-result] callback. Success returns one
   caller-owned :module-data plus immutable descriptive :metadata; caller releases
   :module-data when done. The original inputs remain caller-owned.

   An IO error returns its owned :io-result for the caller to inspect/release.
   Validation failures expose :checkpoint/:io-result for recovery. No initialization
   runs and no publication, provenance, or kernel authority is manufactured."
  ([world invoke environment expected-module]
   (export-classic world invoke environment expected-module {}))
  ([world invoke environment expected-module {:keys [helper] :or {helper export-helper}}]
   (let [expected (name-value world expected-module)
         [world result] (invoke (-> world (m/retain environment 1) (m/retain expected-module 1))
                                helper [environment expected-module m/erased])
         node (when (m/ref? result) (m/node world result))]
     (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node))
                    (bridge/constructor-layout? node 1 0))
       (fail "Malformed source module IO result" {:checkpoint world :io-result result}))
     (if (= 1 (:tag node)) {:world world :status :io-error :io-result result}
       (try
         (let [pair (first (:fields node)) [data text] (:fields (ctor world pair 2 0))
               text (string/string-value {:ref? m/ref? :node m/node} world text)
               metadata (validate-metadata world expected data text)
               world (-> world (m/retain data 1) (m/release result 1) (assoc :result 0))]
           {:world world :status :ok :module-data data :metadata metadata})
         (catch Throwable cause
           (throw (ex-info (or (.getMessage cause) "Invalid source module export")
                           (assoc (ex-data cause) :checkpoint world :io-result result) cause))))))))
