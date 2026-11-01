(ns java-matched-prelude-module-v4
  "Fixed byte-authenticated native ModuleData capability. Only prepare! can issue
   Prepared and only its actual install can issue a live ModuleLease. This grants
   data provenance, not proof replay, executable IR or kernel association."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j] [java-ir-module-data-graph :as graph]
            [ansatz.research.ir.source-setup :as source])
  (:import [java.util WeakHashMap] [java.lang.reflect InvocationTargetException]))
(def audit-pin "a0f2f5cb95e762a976514ec570f2eff7c810b9ea9b2d90aed55889473d5287c2")
(def module-name ["str" ["str" ["anonymous"] "Init"] "Prelude"])
(def files #{"build-cohort.json" "correspondence.json" "kernel.ndjson" "module-data.jsonl"
             "module-file-cohort.json" "transport-receipt.json" "typed-scalars.json"})
(deftype Prepared [])
(deftype ModuleLease [])
(defonce ^:private prepared (WeakHashMap.))
(defonce ^:private leases (WeakHashMap.))
(defonce ^:private attempted-engines (WeakHashMap.)) ; immutable marker, no engine-retaining value
(defn- need [condition message] (when-not condition (throw (ex-info message {:profile :matched-prelude-module-v4}))))
(defn- read-entry [registry token message]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info message {})))))
(defn- field [x key] (.get (doto (.getDeclaredField (class x) key) (.setAccessible true)) x))
(defn- guard-node [engine method value]
  (try (.invoke (doto (.getDeclaredMethod (class engine) method (into-array Class [Object])) (.setAccessible true)) engine (object-array [value]))
       (catch InvocationTargetException error (throw (.getCause error)))))
(defn- typed-json [dir audit filename maximum]
  (source/checked-json (io/file dir filename) (get-in audit ["files" filename "sha256"]) maximum))
(defn- legacy-input! [input]
  (let [requested {"importAll" false "isExported" true "isMeta" false "module" module-name}
        effective {"importAll" true "isExported" false "isMeta" false "module" module-name}
        modules (get input "modules") mod (first modules)]
    (need (and (= "lean-module-data-input/1" (get input "schema")) (= "private" (get input "globalLevel"))
               (= source/lean-pin (get input "leanCommit")) (= "4.33.1" (get input "leanVersion"))
               (false? (get input "nativeEnvironmentFinalized")) (false? (get input "regionAddressesTransported"))
               (true? (get input "transitiveClosure")) (= [requested] (get input "requestedImports"))
               (= 1 (count modules)) (= module-name (get mod "module")) (= effective (get mod "effectiveImport"))
               (= [0 1 2] (mapv #(get % "rootIndex") (get mod "parts")))
               (= [3 4] (mapv #(get % "rootIndex") (get mod "irParts")))
               (= 2314 (get-in mod ["parts" 2 "moduleData" "constantCount"])))
          "Fixed legacy requested/effective Prelude input differs")
    input))
(defn prepare!
  "Verify fixed audit/all seven byte hashes and typed claims, then invoke the
   actual bounded converter itself. No caller graph, digest or root is accepted."
  [basis pair-directory]
  (let [dir (if (instance? java.nio.file.Path pair-directory) (.toFile ^java.nio.file.Path pair-directory) (io/file pair-directory))
        audit (source/checked-json (io/file dir "pair-audit.json") audit-pin 65536)
        _ (need (and (= "matched-prelude-pair-audit/1" (get audit "schema")) (= files (set (keys (get audit "files"))))
                     (= 2314 (get audit "declarations")) (= 134363 (get audit "moduleDataRecords"))
                     (= "legacy-prelude-explicit-Init.Prelude/1" (get audit "sourceHeaderProfile"))
                     (every? true? (map #(get audit %) ["checkingShapesEqual" "dependencyClosure" "displayKeyCollisionFree" "familyClosure"
                                                        "fullBodies" "structuralExprKeys" "sourceCIIndicesComplete" "typedNameCollisionFree" "quotInit"]))
                     (every? false? (map #(get audit %) ["generatedIRAuthorized" "guestFinalizationAccepted" "proofReplay"]))) "Fixed paired audit profile differs")
        _ (doseq [[filename metadata] (get audit "files")]
            (let [file (io/file dir filename) n (get metadata "bytes")]
              (need (and (integer? n) (<= 1 n (* 32 1024 1024)) (= n (.length file))
                         (= (get metadata "sha256") (source/file-sha file))) "Fixed paired file bytes/hash differ")))
        typed (typed-json dir audit "typed-scalars.json" (* 128 1024))
        corr (typed-json dir audit "correspondence.json" (* 2 1024 1024))
        build (typed-json dir audit "build-cohort.json" 65536)
        _ (need (and (= source/lean-pin (get build "leanCommit")) (= "Lean.ExprStructEq/Expr.equal" (get build "exporterCacheEquality"))
                     (= "matched-prelude-source-correspondence/1" (get corr "schema")) (= "full" (get corr "bodyPolicy"))
                     (true? (get corr "quotInit")) (= 2314 (count (get corr "constants")))) "Paired source/correspondence cohort differs")
        _ (legacy-input! (get corr "source"))
        claims (get typed "claims") graph-sha (get-in audit ["files" "module-data.jsonl" "sha256"])
        _ (need (and (= "matched-prelude-typed-scalars/1" (get typed "schema")) (= 2147483647 (get typed "threshold"))
                     (= 481 (get typed "claimCount") (count claims))
                     (= {"Lean.Name.num" 479 "Lean.Literal.natVal" 1 "Lean.IR.LitVal.num" 1} (frequencies (map #(get % "sourceType") claims)))) "Typed native scalar census differs")
        slots (into {} (for [claim claims]
                         (do (need (and (= "Nat" (get claim "domain"))
                                        (integer? (get claim "nodeId")) (<= 0 (get claim "nodeId") 134362)
                                        (integer? (get claim "fieldIndex")) (<= 0 (get claim "fieldIndex") 255)
                                        (string? (get claim "value")) (re-matches #"[1-9][0-9]*" (get claim "value"))
                                        (< Integer/MAX_VALUE (bigint (get claim "value")) Long/MAX_VALUE)) "Invalid actual typed scalar claim")
                             [[graph-sha (get claim "nodeId") (get claim "fieldIndex") (get claim "value")] :nat])))
        _ (need (= 481 (count slots)) "Duplicate native scalar claims")
        ctx (j/prepare-host-program basis [] [])
        native-source (j/source-binding ctx {"schema" "fixed-matched-prelude-native-data/4" "pair-audit-sha256" audit-pin "module-data-sha256" graph-sha})
        state-token (Object.)
        converted (graph/prepare ctx native-source state-token (io/file dir "module-data.jsonl") {:sha256 graph-sha :domain #(get slots %)})
        census (:census converted)
        _ (need (= (set (keys slots)) (set (map #(into [graph-sha] %) (:ambiguous-immediates census)))) "Typed claims do not exactly cover actual source slots")
        _ (need (= 131669 (:normalized-nodes census)) "Fixed Java normalization count differs")
        ;; Converter manifest uses keyword keys. Normalize the already bounded,
        ;; immutable input explicitly to native producer JSON key spelling.
        input-json (json/read-str (json/write-str (:input (:manifest census))))
        _ (legacy-input! input-json)
        token (Prepared.) entry {:state :prepared :basis ctx :graph (:graph converted) :native-source native-source :state-token state-token
                                 :audit audit :correspondence corr :input input-json :census census}]
    (locking prepared (.put prepared token (atom entry))) token))
(defn- driver-live! [entry]
  (let [driver (:driver entry) ctx @(:current-ctx driver) engine (:engine driver)]
    (need (identical? (:thread entry) (Thread/currentThread)) "Module lease is thread confined")
    (need (and (some? (:source driver))
               (identical? (class (:source driver)) (class (:native-source entry)))
               (identical? engine (:engine entry)) (identical? (:source driver) (:code-source entry))
               (identical? (:class ctx) (class engine)) (identical? (:program ctx) (field engine "program"))) "Module lease engine/source/Program differs")
    (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]] (need (false? (field engine key)) "Module lease engine lifecycle stopped"))
    ctx))
(defn- install-raw! [ctx engine graph]
  ;; Capture the actual Java output table without the reflection adapter's vec
  ;; allocation between guest-root publication and recording its owned slot.
  (try (.invoke (.getMethod ^Class (:class ctx) "installGraph" (into-array Class [(class graph)])) engine (object-array [graph]))
       (catch InvocationTargetException error (throw (.getCause error)))))
(defn install!
  "Reuse immutable Prepared data across fresh engines; one actual install attempt
   per engine. A failed engine cannot retry. Actual returned output tables and
   pending/owned aggregate occurrences are preserved before validation."
  [token driver]
  (let [cell (read-entry prepared token "Actual fixed Prepared required") s @cell ctx @(:current-ctx driver) engine (:engine driver)
        owner (object-array [nil :install-pending]) outputs-holder (object-array 1) lease (ModuleLease.)
        state (atom (assoc (dissoc s :graph :state :basis) :status :install-pending :thread (Thread/currentThread) :driver driver :engine engine
                           :code-source (:source driver) :owner owner :outputs outputs-holder))]
    (need (= :prepared (:state s)) "Actual immutable Prepared state differs")
    (need (and (identical? (:class (:basis s)) (:class ctx)) (= "idle" (j/phase ctx engine))) "Prepared/driver class or idle boundary differs")
    (driver-live! @state)
    (locking attempted-engines
      (need (not (.containsKey attempted-engines engine)) "Module install was already attempted on this engine")
      (.put attempted-engines engine true))
    (locking leases (.put leases lease state))
    (try
      (let [outputs ^objects (install-raw! ctx engine (:graph s))]
        (aset ^objects outputs-holder 0 outputs)
        (need (= 1 (alength outputs)) "Module import did not return one aggregate owner")
        (aset ^objects owner 0 (aget outputs 0)) (aset ^objects owner 1 :owned)
        (let [array (guard-node engine "array" (aget outputs 0)) provenance (field engine "preparedModuleSource")]
          (need (and (= 5 (.arraySize array)) (identical? (:native-source s) (field provenance "binding"))
                     (identical? (:state-token s) (field provenance "acceptedStateToken"))) "Actual installed aggregate/source differs"))
        (swap! state assoc :status :live)
        lease)
      (catch Throwable cause
        (swap! state assoc :status :failed)
        (throw (ex-info "Fixed module install failed; preserve its actual owner packet" {:module-lease lease} cause))))))
(defn inspect! [lease]
  (let [s @(read-entry leases lease "Actual installed ModuleLease required")]
    (need (= :live (:status s)) "Module lease is failed or retired")
    (driver-live! s)
    (need (= :owned (aget ^objects (:owner s) 1)) "Module aggregate occurrence was transferred")
    (let [aggregate (aget ^objects (:owner s) 0) array (guard-node (:engine s) "array" aggregate)
          provenance (field (:engine s) "preparedModuleSource")]
      (need (and (= 5 (.arraySize array)) (identical? (:native-source s) (field provenance "binding"))
                 (identical? (:state-token s) (field provenance "acceptedStateToken"))) "Installed native aggregate/source changed")
      {:aggregate aggregate :engine (:engine s) :basis (driver-live! s) :code-source (:code-source s) :native-source (:native-source s)
       :input (:input s) :audit-pin audit-pin :audit (:audit s) :correspondence (:correspondence s) :census (:census s)})))
(defn borrow! [lease f]
  (let [result (f (inspect! lease))] (inspect! lease) result))
(defn owner-packet [lease]
  (select-keys @(read-entry leases lease "Actual installed ModuleLease required") [:status :owner :outputs]))
(defn take-retirement-owner! [lease]
  (let [cell (read-entry leases lease "Actual installed ModuleLease required") s @cell]
    (inspect! lease)
    (need (= "idle" (j/phase (driver-live! s) (:engine s))) "Module retirement requires IDLE")
    (let [value (aget ^objects (:owner s) 0)]
      (aset ^objects (:owner s) 1 :external-retirement) (reset! cell {:status :retired})
      value)))
