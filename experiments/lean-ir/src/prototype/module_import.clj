(ns prototype.module-import
  "Assemble transported data through pinned guest import helpers, execute guest
   finalizeImport, and strictly associate its FINAL checked constant map.
   No native Environment pointers or copied native extension states are accepted.
   Input ModuleData roots are borrowed; successful :environment is caller-owned."
  (:require [clojure.string :as str] [clojure.data.json :as json]
            [prototype.machine :as m] [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as kernel] [prototype.runtime-prim :as prim]
            [prototype.native-scalar :as native]
            [prototype.runtime-string :as string])
  (:import [ansatz.kernel Env]))

(defn- target [namespace part]
  ["str" ["str" ["anonymous"] namespace] part])
;; The inferred unboxed entry borrows modules. Its standard boxed adapter
;; explicitly consumes both object arrays and releases the borrowed first input.
(def bulk-helper ["str" (target "ModuleDataTransport" "batchAssemble") "_boxed"])
(def header-finalize-helper (target "ModuleDataTransport" "finalizeTransportForHeader"))
(def helpers
  {:part (target "ModuleDataTransport" "mkVirtualPart")
   :request (target "ModuleDataTransport" "mkRequestedImport")
   :module (target "ModuleDataTransport" "mkImportedModule")
   :state (target "ModuleDataTransport" "assembleImportState")
   :finalize (target "ModuleDataTransport" "finalizeTransport")
   :root (target "KernelBridgeShim" "checkedKernelRoot")
   :constant-map (target "KernelBridgeShim" "checkedConstantMapRoot")
   :constants (target "KernelBridgeShim" "checkedConstants")
   :quot-init? (target "KernelBridgeShim" "checkedQuotInit")})
(defn- fail [message data] (throw (ex-info message data)))
(defn- flag! [value]
  (when-not (boolean? value) (fail "Import metadata requires explicit Bool" {:value value}))
  (if value 1 0))

(defn module-string
  "Lossless conversion for the guest helpers' String.toName boundary.
   Numeric or dotted/empty individual Name segments need a future typed-Name
   helper; do not silently change their identity by printing and reparsing."
  [encoded]
  (loop [name encoded parts []]
    (cond
      (= ["anonymous"] name)
      (if (seq parts) (str/join "." (reverse parts))
        (fail "Anonymous module names are unsupported" {}))
      (and (vector? name) (= 3 (count name)) (= "str" (first name))
           (string? (nth name 2)) (seq (nth name 2))
           (not (.contains ^String (nth name 2) ".")))
      (recur (second name) (conj parts (nth name 2)))
      :else (fail "Module name cannot roundtrip through String.toName" {:name encoded}))))

(defn- array! [world value]
  (when-not (and (m/ref? value) (= :array (:kind (m/node world value))))
    (fail "Expected guest import array" {:value value}))
  (:fields (m/node world value)))
(defn- module-data! [world value]
  (when-not (and (m/ref? value) (= 0 (:tag (m/node world value)))
                 (bridge/constructor-layout? (m/node world value) 5 1))
    (fail "Expected transported ModuleData" {:value value}))
  (m/node world value))
(defn- import-metadata! [import]
  (module-string (:module import))
  (doseq [flag [:importAll :isExported :isMeta]] (flag! (get import flag))) import)

(defn- standalone-module [world requested modules]
  (when-not (and (= 1 (count modules)) (= 1 (count requested)))
    (fail "Standalone import requires exactly one dependency-free classic module" {}))
  (let [mod (first modules) request (first requested) parts (:parts mod)
        _ (when-not (and (= (:module mod) (:module request)) (= 1 (count parts)) (empty? (:irParts mod)))
            (fail "Standalone import requires one exact classic data part and no IR parts" {}))
        node (module-data! world (:value (first parts)))
        ;; This is an actual guest import-array check, not a summary-count hint.
        _ (when (seq (array! world (first (:fields node))))
            (fail "Standalone import has unresolved module dependencies" {}))
        _ (when-not (= 0 (m/read-scalar-node node {:index 5 :offset 0 :type "uint8" :region :scalar}))
            (fail "Standalone import requires a classic non-module artifact" {}))]
    [(assoc mod :effectiveImport request :hasData true :needsIRTrans false
                :irPhases (if (:isMeta request) "comptime" "runtime"))]))

(defn- inputs! [loaded options]
  (let [manifest (:manifest loaded) world (:world loaded)
        requested (get-in manifest [:input :requestedImports]) modules (:modules loaded)
        module-system? (get options :module-system? false)
        _ (when-not (boolean? module-system?)
            (fail "Import header module-system? must be an explicit Bool" {}))
        expected-level (if module-system? "exported" "private")]
    (when-not (= expected-level (get-in manifest [:input :globalLevel]))
      (fail "Import producer visibility does not match the requested header mode"
            {:module-system? module-system? :expected-level expected-level
             :actual-level (get-in manifest [:input :globalLevel])}))
    (when-not (and (= "lean-module-dag/1" (:schema manifest)) (= 64 (:wordBits manifest))
                   (= "little" (:byteOrder manifest))
                   (= "unsigned-native-tagged-payload" (:immediateEncoding manifest))
                   (= "4.33.1" (get-in manifest [:input :leanVersion]))
                   (= (get prim/pinned-build "lean_get_githash") (get-in manifest [:input :leanCommit]))
                   (false? (get-in manifest [:input :nativeEnvironmentFinalized]))
                   (false? (get-in manifest [:input :regionAddressesTransported]))
                   (vector? requested) (vector? modules))
      (fail "Unsupported guest import producer/profile" {}))
    (doseq [request requested] (import-metadata! request))
    (let [modules (if (true? (get-in manifest [:input :transitiveClosure])) modules
                    (if (:allow-standalone? options) (standalone-module world requested modules)
                      (fail "Guest imports require a transported transitive closure" {})))
          names (mapv :module modules)]
      (when-not (= (count names) (count (set names))) (fail "Duplicate transported import module" {}))
      (doseq [mod modules]
        (module-string (:module mod))
        (import-metadata! (:effectiveImport mod))
        (when-not (= (:module mod) (get-in mod [:effectiveImport :module]))
          (fail "Effective import module/name mismatch" {}))
        (flag! (:hasData mod)) (flag! (:needsIRTrans mod))
        (when-not (contains? #{"runtime" "comptime" "all"} (:irPhases mod))
          (fail "Unsupported import IR phase" {:phase (:irPhases mod)}))
        (when-not (and (vector? (:parts mod)) (vector? (:irParts mod)))
          (fail "Import parts must preserve their native order" {})))
      (doseq [request requested]
        (when-not (contains? (set names) (:module request)) (fail "Requested import missing from transported closure" {:request request})))
      (when module-system?
        ;; Native importModulesCore rejects direct classic imports at exported
        ;; visibility. Examine the actual public ModuleData, not summary flags.
        (let [by-name (into {} (map (juxt :module identity)) modules)]
          (doseq [request requested]
            (let [part (first (:parts (get by-name (:module request))))
                  node (module-data! world (:value part))]
              (when-not (= 1 (m/read-scalar-node node {:index 5 :offset 0 :type "uint8" :region :scalar}))
                (fail "Module-system imports require module artifacts" {:module (:module request)}))))))
      {:modules modules :requested requested})))

(defn- part-input! [world part]
  (let [data (:value part) _ (module-data! world data)
        {:keys [filePath mappedBytes oleanVersion leanCommit]} (:artifact part)]
    (when-not (and (string? filePath) (seq filePath) (not (.contains ^String filePath "\u0000"))
                   (integer? mappedBytes) (<= 0 mappedBytes Long/MAX_VALUE)
                   (= 2 oleanVersion) (= (get prim/pinned-build "lean_get_githash") leanCommit))
      (fail "Invalid transported import part provenance" {:artifact (:artifact part)}))
    [data filePath mappedBytes]))

(defn- parts [world invoke target parts]
  (let [[world values]
        (reduce (fn [[world out] part]
                  (let [[data filePath mappedBytes] (part-input! world part)
                        ;; Receiver keeps its owner; constructor consumes another.
                        [world pair] (invoke (m/retain world data 1) target [data filePath mappedBytes])]
                    [world (conj out pair)])) [world []] parts)]
    (m/allocate world :array 246 values)))

(defn- bulk-parts [world parts]
  (let [[world values]
        (reduce (fn [[world out] part]
                  (let [[data path bytes] (part-input! world part)
                        [world input] (m/allocate (m/retain world data 1) :ctor 0 [data path bytes])]
                    [world (conj out input)])) [world []] parts)]
    (m/allocate world :array 246 values)))

(defn- assemble-bulk [loaded invoke options modules requested]
  ;; Validate EVERY part before a guest call or transfer. Records use only object
  ;; fields, so no host imitation of native scalar padding is involved.
  (doseq [mod modules part (concat (:parts mod) (:irParts mod))]
    (part-input! (:world loaded) part))
  (let [[world module-inputs]
        (reduce (fn [[world out] mod]
                  (let [effective (:effectiveImport mod)
                        [world parts] (bulk-parts world (:parts mod))
                        [world ir-parts] (bulk-parts world (:irParts mod))
                        fields [(module-string (:module mod)) (flag! (:importAll effective))
                                (flag! (:isExported effective)) (flag! (:isMeta effective))
                                (get {"runtime" 0 "comptime" 1 "all" 2} (:irPhases mod))
                                (flag! (:hasData mod)) (flag! (:needsIRTrans mod)) parts ir-parts]
                        [world input] (m/allocate world :ctor 0 fields)]
                    [world (conj out input)])) [(:world loaded) []] modules)
        [world module-array] (m/allocate world :array 246 module-inputs)
        [world request-inputs]
        (reduce (fn [[world out] request]
                  (let [fields [(module-string (:module request)) (flag! (:importAll request))
                                (flag! (:isExported request)) (flag! (:isMeta request))]
                        [world input] (m/allocate world :ctor 0 fields)]
                    [world (conj out input)])) [world []] requested)
        [world request-array] (m/allocate world :array 246 request-inputs)
        target (or (get-in options [:helpers :batch]) bulk-helper)
        [world pair] (invoke world target [module-array request-array])
        node (when (m/ref? pair) (m/node world pair))]
    (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 2 (count (:fields node))))
      (fail "Malformed guest batch import assembly result" {:checkpoint world :pair pair}))
    (let [[state imports] (:fields node)
          _ (array! world imports)
          world (-> world (m/retain state 1) (m/retain imports 1) (m/release pair 1))]
      {:world (assoc world :result 0) :state state :imports imports :modules modules :requested requested})))

(defn assemble
  "Borrow receiver roots, return owned :state and :imports for finalizeTransport.
   Uses the real guest constructors; does not finalize or check declarations.
   :assembly :bulk uses one real guest batchAssemble call with validated
   object-only input records; default :sequential retains the original path.
   :allow-standalone? admits only a proven dependency-free classic single file."
  ([loaded invoke] (assemble loaded invoke {}))
  ([loaded invoke options]
   (let [{:keys [modules requested]} (inputs! loaded options)
         assembly (get options :assembly :sequential)]
     (when-not (contains? #{:sequential :bulk} assembly)
       (fail "Unknown guest import assembly strategy" {:assembly assembly}))
     (if (= :bulk assembly)
       (assemble-bulk loaded invoke options modules requested)
       (let [targets (merge helpers (:helpers options))
         [world imported]
         (reduce (fn [[world out] mod]
                   (let [effective (:effectiveImport mod)
                         [world data] (parts world invoke (:part targets) (:parts mod))
                         [world ir] (parts world invoke (:part targets) (:irParts mod))
                         args [(module-string (:module mod)) (flag! (:importAll effective)) (flag! (:isExported effective))
                               (flag! (:isMeta effective)) (get {"runtime" 0 "comptime" 1 "all" 2} (:irPhases mod))
                               (flag! (:hasData mod)) (flag! (:needsIRTrans mod)) data ir]
                         [world imported] (invoke world (:module targets) args)]
                     [world (conj out imported)])) [(:world loaded) []] modules)
         [world array] (m/allocate world :array 246 imported)
         [world state] (invoke world (:state targets) [array])
         [world requests]
         (reduce (fn [[world out] request]
                   (let [args [(module-string (:module request)) (flag! (:importAll request))
                               (flag! (:isExported request)) (flag! (:isMeta request))]
                         [world request] (invoke world (:request targets) args)]
                     [world (conj out request)])) [world []] requested)
         [world imports] (m/allocate world :array 246 requests)]
     {:world (assoc world :result 0) :state state :imports imports :modules modules :requested requested})))))

(defn project-finalizer-flag-progress
  "Project the genuine header's quotient metadata, preserving actual helper
   progress and :finalizer-temporary-owners on failure. Adds no primitives."
  [world environment invoke targets certificate attestation]
  (let [progress (volatile! world) owners (volatile! []) stage (volatile! :header-preflight)
        call (fn [world target args]
               (vreset! stage [:header-helper target])
               (let [[world value] (invoke world target args)]
                 (vreset! progress world) (vswap! owners conj value) [world value]))
        release (fn [world value]
                  (vreset! stage :header-release)
                  (let [world (m/release world value 1)]
                    (vreset! progress world) (vswap! owners #(vec (rest %))) world))]
   (try
  (if-not attestation [world certificate]
    (let [{:keys [requested-imports header-helper]} attestation
          _ (when-not (and (vector? requested-imports) (vector? header-helper))
              (fail "Invalid explicit finalizer attestation" {}))
          _ (doseq [request requested-imports] (import-metadata! request))
          [world text] (call world header-helper [environment])
          header (json/read-str (string/string-value {:ref? m/ref? :node m/node} world text) :key-fn keyword)
          world (release world text)
          _ (when-not (and (= "lean-source-import-header/1" (:schema header))
                           (= "SourceModuleImport.finalizerHeader" (:producer header))
                           (= (get prim/pinned-build "lean_get_githash") (:leanCommit header))
                           (false? (:moduleSystem header)) (= requested-imports (:imports header)))
              (fail "Actual finalizer header differs from explicit import attestation" {}))
          [world flag-value] (call world (:quot-init? targets) [environment])
          flag (native/nat-value {:ref? m/ref? :node m/node} world flag-value)
          _ (when-not (= (if (seq requested-imports) 1 0) flag)
              (fail "Finalizer quotient flag differs from pinned import-header rule" {}))
          world (release world flag-value)]
      ;; This projects metadata only. enableQuot adds NO ConstantInfo/primitives;
      ;; canonical Quot CI checking above remains strict and unchanged.
      [world (if (= 1 flag) (update certificate :env #(.enableQuot ^Env %)) certificate)]))
   (catch Throwable cause
     (throw (ex-info (or (.getMessage cause) "Finalizer header projection failed")
                     (merge {:checkpoint @progress :finalizer-stage @stage}
                            (ex-data cause) {:finalizer-temporary-owners @owners}) cause))))))

(defn- project-finalizer-flag [world environment invoke targets certificate attestation]
  (project-finalizer-flag-progress world environment invoke targets certificate attestation))

(defn finish-finalization
  "Consume the owned IO.Result of an actual guest import finalizer and strictly
   associate its final checked map. This also completes a resumed finalizer:
   callers must supply its actual world/result, not reconstruct an Environment.
   Guest errors remain owned in :io-result; success owns :environment.
   Default quotient-state association remains strict. Optional trusted
   :finalizer-attestation {:requested-imports exactHeader :header-helper Name}
   projects the actual private/classic finalizer's !imports.isEmpty quotient
   metadata only AFTER all constants pass strict checking. It adds no primitives.
   Failures preserve a cause's latest checkpoint/session and named owners. The
   original owned IO snapshot is separate under :finalizer-result; the owned
   Environment at checking entry is paired under :finalization-entry. These are
   diagnostic alternatives, never permission to retry effects. The original raw
   session is caller-held; this function cannot reconstruct it from INVOKE."
  ([world result invoke] (finish-finalization world result invoke {}))
  ([world result invoke options]
   (let [targets (merge helpers (:helpers options))
         finalizer-result {:checkpoint world :io-result result}
         node (when (m/ref? result) (m/node world result))]
     (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node)) (= 1 (count (:fields node))))
       (fail "Malformed guest import IO.Result" {:checkpoint world :io-result result :finalizer-result finalizer-result}))
     (if (= 1 (:tag node))
       {:status :io-error :world world :io-result result}
       (let [environment (first (:fields node))
             _ (when-not (m/ref? environment) (fail "Guest import did not return an Environment reference"
                       {:checkpoint world :io-result result :finalizer-result finalizer-result}))
             world (-> world (m/retain environment 1) (m/release result 1) (assoc :result 0))]
         (try
           (let [[world constants] (invoke world (:constants targets) [environment])
                 values (array! world constants)
                 certificate (kernel/verify-constants world values (:kernel-policy options))
                 world (m/release world constants 1)
                 [world certificate] (project-finalizer-flag world environment invoke targets certificate
                                                              (:finalizer-attestation options))
                 world (kernel/associate-checked {:invoke invoke} world environment targets certificate)]
             {:status :ok :world (assoc world :result 0) :environment environment :certificate certificate})
           (catch Exception cause
             (let [data (ex-data cause) newer? (some? (:checkpoint data))]
               (throw (ex-info "Guest import kernel association failed"
                         (cond-> (merge {:phase :kernel-association} data
                                   {:checkpoint (or (:checkpoint data) world)
                                    :finalizer-result finalizer-result
                                    :finalization-entry {:checkpoint world :environment environment}})
                           ;; A child checkpoint may have consumed or changed
                           ;; this owner. Do not pair an entry-world Env with it.
                           (not newer?) (assoc :environment environment)
                           (:checkpoint-session data) (assoc :session (:checkpoint-session data)))
                         cause))))))))))

(defn import-loaded
  "Execute real guest finalization, then strictly check its final checked map.
   invoke [world structuredTarget rawArgs] -> [world rawResult] follows typed
   guest argument ownership. :kernel-policy explicitly authorizes assumptions/
   unsafe declarations if needed. Success returns caller-owned :environment and
   a world-local checked-root anchor. Guest IO failure returns owned :io-result.
   Host checking failure preserves the latest checkpoint and paired owned
   finalization snapshots for inspection.
   Neither failure creates a Java association for an unchecked nonempty root."
  ([loaded invoke] (import-loaded loaded invoke {}))
  ([loaded invoke options]
   (let [targets (merge helpers (:helpers options))
         {:keys [world state imports]} (assemble loaded invoke options)
         [world result] (if (:module-system? options)
                          (invoke world (or (:header-finalize targets) header-finalize-helper)
                                  [state imports 1 m/erased])
                          (invoke world (:finalize targets) [state imports m/erased]))]
     (finish-finalization world result invoke options))))
