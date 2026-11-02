(ns ansatz.lean.jvm.startup
  "Interpreted startup ledger; only the fixed research publisher currently issues Prepared."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [ansatz.lean.jvm.ir :as j]
            [ansatz.lean.jvm.capabilities :as caps]
            [ansatz.lean.jvm.original :as original])
  (:import [java.lang ClassValue]
           [java.nio.file Files LinkOption StandardOpenOption OpenOption]
           [java.nio.file.attribute BasicFileAttributes]
           [java.security MessageDigest] [java.util WeakHashMap] [java.util.concurrent.locks ReentrantLock]))

(def ^:private current-capture-sha "f644f89c61f672569743eb11ad6874cb35028b3e4097554f4b96145b54e32ea0")
(def ^:private codec-sha "53b224c8fa037b144260872e3b14878aff86dbb61b598e1ea49f991dabc1fb6b")
(deftype Prepared [])
(deftype Startup [])
(defonce ^:private prepared-registry (WeakHashMap.))
(defonce ^:private startup-registry (WeakHashMap.))
(defn- put-issued! [registry token cell]
  (locking registry (.put ^WeakHashMap registry token cell)) token)
(defn- need [p message] (when-not p (throw (ex-info message {:profile :interpreted-startup-research-v1}))))
(defn- sha [bytes] (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))))
(defn- vector! [x limit] (need (and (vector? x) (<= (count x) limit)) "Expected bounded immutable vector") x)
(defn- name! [x]
  (loop [x x depth 0]
    (need (< depth 256) "Typed Name exceeds depth limit")
    (if (= x ["anonymous"]) x
        (do (need (and (vector? x) (= 3 (count x)) (#{"str" "num"} (x 0))
                       (string? (x 2)) (<= (count (x 2)) 4096)) "Malformed typed Name")
            (when (= "num" (x 0))
              (need (and (re-matches #"0|[1-9][0-9]{0,19}" (x 2))
                         (<= (bigint (x 2)) 18446744073709551615N)) "Name numeral exceeds UInt64"))
            (recur (x 1) (inc depth))))))
(defn- pair! [x]
  (need (and (vector? x) (= 2 (count x))) "Malformed initializer pair")
  (doseq [name x] (name! name)) x)

(defn module-plan
  "Pure descriptive validation, not an issuer. Preserve first-list duplicates exactly."
  [module in-server]
  (let [first-list (vector! (get module "regularModuleEntries") 128)
        ir-list (vector! (get module "regularIREntries") 128)
        _ (doseq [pair (concat first-list ir-list)] (pair! pair))
        sequence (into first-list (remove (set first-list) ir-list))
        phase (get-in module ["effectiveImport" "irPhases"])
        init-runtime (or in-server (not= phase "runtime"))
        decisions (vector! (get module "phaseDecisions") 256)
        _ (need (#{"runtime" "comptime" "all"} phase) "Unsupported effective IR phase")
        _ (need (and (boolean? in-server) (= init-runtime (get module "initRuntime"))
                     (= sequence (vector! (get module "regularSequence") 256))
                     (= (count sequence) (count decisions))) "Initializer sequence/phase metadata differs")]
    (doseq [key ["builtinModuleEntries" "builtinIREntries"]]
      (need (empty? (vector! (get module key) 128)) "Builtin initialization unsupported in this profile"))
    (mapv (fn [ordinal pair decision]
            (pair! (get decision "pair"))
            (let [decl-phase (get decision "declarationIRPhases")
                  selected (or init-runtime (not= decl-phase "runtime"))]
              (need (and (#{"runtime" "comptime" "all"} decl-phase)
                         (= ordinal (get decision "ordinal")) (= pair (get decision "pair"))
                         (= selected (get decision "selected"))) "Initializer phase decision differs")
              (need (not= ["anonymous"] (second pair)) "Anonymous regular initialization unsupported")
              {:ordinal ordinal :pair pair :selected selected}))
          (range) sequence decisions)))

(defn validate-capture
  "Reusable data validator. Native checker evidence is trusted only after authenticated publication."
  [capture]
  (need (= "lean-native-startup-evidence/1" (get capture "schema")) "Startup schema differs")
  (need (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get capture "leanCommit")) "Compiler cohort differs")
  (need (and (= "legacy-private-ordinary/1" (get capture "profile"))
             (false? (get-in capture ["actualHeader" "isModule"]))
             (= "private" (get-in capture ["actualHeader" "globalLevel"]))
             (empty? (vector! (get capture "unsupportedActivationReasons") 256))
             (= 0 (get capture "dynamicAPSites"))) "Unsupported startup profile")
  (need (= (get-in capture ["request" "requestedImports"])
           (get-in capture ["actualHeader" "imports"]) (get capture "requestedImports"))
        "Original request/header imports differ")
  (let [modules (vector! (get capture "modules") 2048)
        rows (vector! (get capture "declarations") 4096)
        actions (vector! (get capture "selectedActions") 256)
        in-server (get-in capture ["actualHeader" "inServer"])
        names (mapv #(get-in % ["effectiveImport" "import" "module"]) modules)
        _ (doseq [name names] (name! name))
        _ (need (= (count names) (count (set names))) "Duplicate effective module")
        _ (need (= names (vector! (get capture "moduleOrder") 2048)) "Effective module order differs")
        plans (mapv (fn [index module]
                      (need (= index (get module "index")) "Module index differs")
                      {:index index :name (names index) :actions (module-plan module in-server)})
                    (range) modules)
        selected (vec (for [m plans a (:actions m) :when (:selected a)]
                        {:moduleIndex (:index m) :module (:name m)
                         :sequenceOrdinal (:ordinal a) :pair (:pair a)}))
        _ (doseq [a actions] (name! (get a "module")) (pair! (get a "pair")))
        actual (mapv #(select-keys % ["moduleIndex" "module" "sequenceOrdinal" "pair"]) actions)
        expected (mapv #(into {} (map (fn [[k v]] [(name k) v]) %)) selected)
        _ (need (= expected actual) "Selected action order differs")
        _ (need (= (count selected) (count (set (map #(first (:pair %)) selected))))
                "Repeated selected global is unsupported before engine allocation")
        _ (doseq [row rows]
            (name! (get row "name"))
            (doseq [dependency (vector! (get row "dependencies") 8192)] (name! dependency)))
        by-name (into {} (map (juxt #(get % "name") identity) rows))]
    (need (= (count rows) (count by-name)) "Duplicate declaration typed Name")
    (doseq [row rows]
      (name! (get row "name"))
      (need (every? #(contains? by-name %) (vector! (get row "dependencies") 8192)) "Incomplete declaration closure"))
    (doseq [a actions]
      (let [[global raw] (get a "pair") e (get a "evidence") boxed (get-in e ["interpreterCallable" "name"])
            signature (fn [n] (let [f (get-in by-name [n "ir" "fdecl"])]
                               {"name" (get f "f") "type" (get f "type") "xs" (get f "xs")}))]
        (need (and (= "named-global" (get e "kind"))
                   (= global (get-in e ["targetCI" "name"]) (get-in e ["globalRaw" "name"]))
                   (= raw (get-in e ["actionCI" "name"]) (get-in e ["actionRaw" "name"])
                      (get-in by-name [global "runtime" "initializer"]))) "Global/action association differs")
        (doseq [[key n] [["globalRaw" global] ["actionRaw" raw] ["interpreterCallable" boxed]]]
          (need (= (get e key) (signature n)) "Original callable signature differs"))
        (doseq [key ["targetCI" "actionCI"]]
          (need (and (false? (get-in e [key "isUnsafe"])) (false? (get-in e [key "isPartial"]))
                     (empty? (get-in e [key "levelParams"]))) "Unsupported initializer CI"))
        (need (= "Lean.Meta.isDefEq" (get-in e ["ioPayloadTypeProof" "algorithm"])) "Missing native type relation")
        (need (and (= "original-interpreter-boxed-lookup" (get e "interpreterSelection"))
                   (= raw (get-in e ["javaTransactionRoute" "name"]))
                   (= "original-raw-not-the-boxed-selection" (get-in e ["javaTransactionRoute" "relationship"]))
                   (= "canonical-erased-unit-zero" (get-in e ["javaTransactionRoute" "world"])))
              "Raw/boxed interpreter selection relationship differs")
        (need (= (get-in e ["actionCI" "type"]) (get-in e ["ioPayloadTypeProof" "actualType"])) "Actual type evidence differs")
        (need (= ["app" ["const" ["str" ["anonymous"] "IO"] []] (get-in e ["targetCI" "type"])]
                 (get-in e ["ioPayloadTypeProof" "expectedType"])) "Expected IO payload type differs")
        (need (= [{"borrow" false "ty" "void" "x" {"idx" 1}}] (get-in e ["actionRaw" "xs"])) "Unsupported raw world ABI")
        (need (= [{"borrow" false "ty" "tagged" "x" {"idx" 1}}] (get-in e ["interpreterCallable" "xs"])) "Unsupported boxed world ABI")
        (need (= "object" (get-in e ["actionRaw" "type"]) (get-in e ["interpreterCallable" "type"])) "Unsupported action result ABI")
        (need (= ["vdecl" {"idx" 2} "object" {"fap" {"c" raw "ys" [{"var" {"id" {"idx" 1}}}]}}
                  ["ret" {"var" {"id" {"idx" 2}}}]] (get-in by-name [boxed "ir" "fdecl" "body"])) "Actual boxed bridge differs")))
    {:modules plans :rows rows :actions actions}))

(defn- read-bounded! [^java.io.InputStream input limit]
  (let [bytes (.readNBytes input (int (inc limit)))]
    (need (<= (alength bytes) limit) "Capture exceeds bound while reading") bytes))
(defn- read-bytes! [path limit]
  (need (and (integer? limit) (<= 1 limit 16777216)) "Invalid capture read bound")
  (let [p (.toPath (io/file path)) options (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])
        attributes #(Files/readAttributes p BasicFileAttributes options)
        stamp (fn [^BasicFileAttributes a] [(.fileKey a) (.size a) (.lastModifiedTime a) (.creationTime a)])
        ^BasicFileAttributes before (attributes)]
    (need (and (.isRegularFile before) (not (.isSymbolicLink before)) (<= (.size before) limit)) "Capture is not a bounded regular file")
    (let [bytes (with-open [input (Files/newInputStream p (into-array OpenOption [StandardOpenOption/READ LinkOption/NOFOLLOW_LINKS]))]
                  (read-bounded! input limit))
          ^BasicFileAttributes after (attributes)]
      (need (and (.isRegularFile after) (not (.isSymbolicLink after)) (= (stamp before) (stamp after))
                 (= (.size after) (alength bytes))) "Capture changed while reading") bytes)))
(defn- compact-entry [entry]
  (let [digest #(sha (.getBytes (json/write-str %) "UTF-8"))]
    (assoc (select-keys entry ["name" "kind" "compiledModule" "levelParams" "selection" "raw" "callable"
                               "semanticArity" "runtimeArity" "argumentPlan" "resultABI" "codecWitnesses" "nativeRepresentation"])
           "typeCheck" (select-keys (get entry "typeCheck") ["signature" "algorithm" "transparency"])
           "nativeEvidence" {"normalizedObservationSHA256" (digest entry)
                             "actualTypeSHA256" (digest (get entry "actualType"))
                             "expectedTypeSHA256" (digest (get-in entry ["typeCheck" "expectedType"]))})))
(defn- publish-prepared! [basis plan rows description codec entries]
  ;; Private implementation shared only by reviewed authenticated publishers.
  (let [requirements (caps/check-rows! basis rows)
        base (j/prepare-host-program basis [] []) source (j/source-binding base description)
        headers (into {} (map (fn [row] [(get row "name") (j/declaration-header source row (sha (.getBytes (json/write-str row) "UTF-8")))]) rows))
        registered (j/register-headers base (mapv #(headers (get % "name")) rows))
        prepared (reduce (fn [ctx row] (if (get-in row ["ir" "fdecl"])
                                       (j/materialize-body ctx (headers (get row "name")) row (mapv headers (original/direct-names row))) ctx)) registered rows)
        ;; Keep runtime method handles and immutable compiled code, never caller
        ;; basis annotations, raw rows, producer documents or compile journals.
        ctx (-> (select-keys prepared [:loader :class :node-class :prepare :constructor :constructor-explicit
                                      :constructor-initializing :function-id :invoke :rbmap :batch :inc :dec :close
                                      :start :start-release :advance :take-result :phase :depth :instructions
                                      :active :tag :rc :fields :scalars :program])
                (assoc :explicit true :initializing true :build-identity (j/supported-build-identity basis)))
        _ (caps/check-program! ctx headers requirements)
        token (Prepared.) cell {:ctx ctx :headers headers :plan (select-keys plan [:modules])
                                :codec codec :entries (mapv compact-entry entries) :requirements requirements}]
    (put-issued! prepared-registry token cell)))
(defn prepare-current! [basis capture-path codec-path]
  ;; Fixed research issuer, never a caller-map capability factory.
  (let [bytes (read-bytes! capture-path 1048576) _ (need (= current-capture-sha (sha bytes)) "Research capture differs")
        capture (json/read-str (String. bytes "UTF-8")) {:keys [rows] :as plan} (validate-capture capture)
        codec (read-bytes! codec-path 65536) _ (need (= codec-sha (sha codec)) "Independent codec witness differs")]
    (publish-prepared! basis plan rows {"startup-research" current-capture-sha} codec [])))
(defn- issued! [registry token klass]
  (need (= klass (class token)) "Foreign startup capability")
  (or (locking registry (.get ^WeakHashMap registry token)) (throw (ex-info "Unknown startup capability" {}))))
(defn open! [prepared capability]
  (let [p (issued! prepared-registry prepared Prepared) ctx (:ctx p)
        cell (atom {:status :opening :prepared p :lock (ReentrantLock.) :module-index 0 :action-index 0
                    :ledger [] :active nil :error-slot (object-array 1) :error-state nil}) token (Startup.)]
    (put-issued! startup-registry token cell)
    (try
      (let [engine (j/machine ctx) _ (swap! cell assoc :engine engine)
            entropy ((:headers p) ["str" ["str" ["anonymous"] "IO"] "getRandomBytes"])
            codec ((:headers p) ["str" ["str" ["anonymous"] "IO"] "userError"])]
        (.invoke (.getMethod ^Class (:class ctx) "installEntropy"
                             (into-array Class [(class capability) (class entropy) (class codec) (class (:codec p))]))
                 engine (object-array [capability entropy codec (:codec p)]))
        (swap! cell assoc :status :running) token)
      (catch Throwable failure (swap! cell assoc :status :host-failed) (throw (ex-info "Startup open failed; preserve packet" {:startup token} failure))))))
(defn- with-lease! [token operation callback]
  (let [cell (issued! startup-registry token Startup) lock (:lock @cell)]
    (need (instance? ReentrantLock lock) "Startup lease is unavailable")
    (.lock ^ReentrantLock lock)
    (try
      (let [owner (:execution-thread @cell)]
        (need (or (nil? owner) (identical? owner (Thread/currentThread))
                  (contains? #{:observe :cancel :abandon} operation))
              "Paused execution cannot change its operation thread")
        (callback))
      (finally (.unlock ^ReentrantLock lock)))))
(defn- live-cell! [token]
  (let [cell (issued! startup-registry token Startup) lock (:lock @cell)]
    (need (and (instance? ReentrantLock lock) (.isHeldByCurrentThread ^ReentrantLock lock))
          "Startup operation requires its serialized lease") cell))
(declare status)
(defn- status-in-lease [token] (select-keys @(live-cell! token) [:status :module-index :action-index :ledger :active :error-state]))
(defn- owner-packet-in-lease [token]
  ;; Trusted diagnostic alias, not an additional owned guest occurrence.
  (select-keys @(live-cell! token) [:status :engine :active :error-slot :error-state :ledger]))
(defonce ^:private field-handles
  ;; ClassValue owns its association through the Class, avoiding a global weak
  ;; Class-key/Field-value backedge. Values contain code metadata, no engines.
  (proxy [ClassValue] []
    (computeValue [cls]
      (into {} (map (fn [^java.lang.reflect.Field field]
                      (.setAccessible field true) [(.getName field) field]) (.getDeclaredFields ^Class cls))))))
(defn- engine-field [engine name]
  (let [field (get (.get ^ClassValue field-handles (class engine)) name)]
    (need field "Runtime lifecycle field is unavailable") (.get ^java.lang.reflect.Field field engine)))
(defn- ready-engine! [prepared engine]
  (need (and (not (engine-field engine "closed")) (not (engine-field engine "disposed"))
             (not (engine-field engine "untrackedFailure"))
             (identical? (get-in prepared [:ctx :program]) (engine-field engine "program"))
             (= "idle" (j/phase (:ctx prepared) engine))
             (false? (j/initializing? (:ctx prepared) engine))
             (not (engine-field engine "pendingOwnedResult"))
             (every? #(nil? (engine-field engine %))
                     ["taskRuntime" "pendingEntropy" "pendingInitializerGlobal" "runtimeAction"
                      "hostRequest" "hostCompletion" "hostGuestRecord" "codeRequest"]))
        "Ready engine/source/program/lifecycle changed"))
(defn- with-ready-engine!-in-lease
  "Internal trusted caller seam, not a public raw-engine export. Callback owns
   decoding/releasing each call result. Failure preserves the actual packet."
  [token callback]
  (let [cell (live-cell! token) {:keys [status prepared engine]} @cell]
    (need (= :ready status) "Startup is not ready")
    (ready-engine! prepared engine)
    (swap! cell assoc :status :calling :execution-thread (Thread/currentThread))
    (try
      (let [answer (callback {:ctx (:ctx prepared) :engine engine :entries (:entries prepared) :headers (:headers prepared)})]
        (ready-engine! prepared engine)
        (swap! cell assoc :status :ready :execution-thread nil) answer)
      (catch Throwable failure
        (swap! cell assoc :status :host-failed)
        (throw (ex-info "Ready engine call failed; preserve actual packet" {:startup token} failure))))))
(defn- call-zero [ctx engine method]
  (.invoke (.getMethod ^Class (:class ctx) method (make-array Class 0)) engine (object-array 0)))
(defn- poll!-in-lease [token budget]
  ;; Argument refusal must never poison an otherwise valid startup.
  (need (and (integer? budget) (<= 1 budget 20000)) "Startup budget must be 1..20000")
  (let [cell (live-cell! token) {:keys [status prepared engine]} @cell ctx (:ctx prepared)]
    (need (= :running status) "Startup is not running; retry refused")
    (try
      (loop [remaining budget]
        (let [{:keys [module-index action-index active ledger]} @cell modules (get-in prepared [:plan :modules])]
          (cond
            (= module-index (count modules))
            (do (j/finish-initialization! ctx engine) (swap! cell assoc :status :ready) (ansatz.lean.jvm.startup/status token))

            active
            (case (j/phase ctx engine)
              "running" (if (pos? remaining)
                          (let [steps (min remaining 128)] (j/advance! ctx engine steps) (recur (- remaining steps)))
                          (ansatz.lean.jvm.startup/status token))
              "complete"
              (let [_ (swap! cell assoc-in [:active :disposition] :complete-pending)
                    result (call-zero ctx engine "completeInitializer")]
                (aset ^objects (:error-slot @cell) 0 result)
                (swap! cell assoc :error-state :owned)
                (let [tag (.getInt ^java.lang.reflect.Field (:tag ctx) result)]
                  (if (= 0 tag)
                    (do (swap! cell assoc :error-state :release-started)
                        (j/release! ctx engine result)
                        (aset ^objects (:error-slot @cell) 0 nil)
                        (swap! cell assoc :error-state nil :active nil :execution-thread nil :action-index (inc action-index))
                        (recur remaining))
                    (do (need (= 1 tag) "Initializer returned malformed IO result")
                        (swap! cell assoc :status :io-error :execution-thread nil) (ansatz.lean.jvm.startup/status token)))))
              (throw (ex-info "Unhandled initializer boundary; preserve packet" {:phase (j/phase ctx engine)})))

            :else
            (let [module (modules module-index) actions (:actions module)]
              (when (= module-index (count ledger))
                (swap! cell update :ledger conj {:name (:name module) :state :entered}))
              (if (= action-index (count actions))
                (do (swap! cell (fn [s] (-> s (assoc-in [:ledger module-index :state] :complete)
                                            (assoc :module-index (inc module-index) :action-index 0))))
                    (recur remaining))
                (let [action (actions action-index)]
                  (if-not (:selected action)
                    (do (swap! cell update :action-index inc) (recur remaining))
                    (if-not (pos? remaining) (ansatz.lean.jvm.startup/status token)
                      (let [[global raw] (:pair action) global ((:headers prepared) global) raw ((:headers prepared) raw)]
                        (swap! cell assoc :execution-thread (Thread/currentThread)
                               :active {:module-index module-index :ordinal action-index :disposition :start-pending})
                        (.invoke (.getMethod ^Class (:class ctx) "startInitializer" (into-array Class [(class global) (class raw)]))
                                 engine (object-array [global raw]))
                        (swap! cell assoc-in [:active :disposition] :running)
                        (recur remaining))))))))))
      (catch Throwable failure
        (swap! cell assoc :status :host-failed)
        (throw (ex-info "Startup failed; preserve actual packet, do not retry" {:startup token} failure))))))
(defn- cancel!-in-lease [token]
  (let [cell (live-cell! token)]
    (need (= :running (:status @cell)) "Startup is terminal")
    (swap! cell assoc :status :cancelled) (ansatz.lean.jvm.startup/status token)))
(defn- release-error!-in-lease [token]
  (let [cell (live-cell! token) {:keys [status error-state prepared engine error-slot]} @cell
        error (aget ^objects error-slot 0)]
    (need (and (= :io-error status) (= :owned error-state)) "No known owned IO error")
    (swap! cell assoc :error-state :release-started)
    (j/release! (:ctx prepared) engine error)
    (aset ^objects error-slot 0 nil)
    (swap! cell assoc :error-state :released :active nil) (ansatz.lean.jvm.startup/status token)))
(defn- closeable-state? [{:keys [status active error-state error-slot]}]
  (and (or (= :ready status) (= :cancelled status)
           (and (= :io-error status) (= :released error-state)))
       (nil? active) (contains? #{nil :released} error-state)
       (some? error-slot) (nil? (aget ^objects error-slot 0))))
(defn- close!-in-lease [token]
  (let [cell (live-cell! token) {:keys [engine prepared] :as state} @cell]
    (need (closeable-state? state) "Startup has active, uncertain, terminal or owned custody")
    (need (= "idle" (j/phase (:ctx prepared) engine)) "Startup must be actually idle to close")
    (swap! cell assoc :status :close-started)
    (.invoke ^java.lang.reflect.Method (:close (:ctx prepared)) engine (object-array 0))
    (reset! cell {:status :closed :lock (:lock @cell)}) nil))

(defn- heap-action-chain! [action entropy-action]
  (let [seen (java.util.IdentityHashMap.)]
    (loop [action action]
      (when action
        (need (and (< (.size seen) 256) (not (.containsKey seen action))
                   (= entropy-action (engine-field action "operation"))
                   (every? #(nil? (engine-field action %)) ["guest" "completion" "request" "task" "scope"]))
              "Abandonment found an unclassified action or resource protocol")
        (.put seen action true) (recur (engine-field action "parent"))))))
(defn- heap-abandonable! [prepared engine]
  (let [requirements (:requirements prepared)]
    (need (= :task-free-captured-output-v1 (:profile requirements)) "Abandonment requires the issued positive pure-heap profile")
    (caps/check-program! (:ctx prepared) (:headers prepared) requirements)
    (when engine
      (need (and (not (engine-field engine "advancing"))
                 (identical? (get-in prepared [:ctx :program]) (engine-field engine "program"))
                 (every? #(nil? (engine-field engine %))
                         ["taskRuntime" "hostRequest" "failedHostRequest" "hostCompletion" "hostGuestRecord"
                          "codeRequest" "failedCodeRequest" "currentTask" "stdioContext" "stdinDefaultRoot" "stderrRoot"
                          "profilingPolicy" "hostGuestPolicy" "exprInstantiationPolicy" "exprTransformPolicy"
                          "shareCommonLayout" "levelInstantiationPolicy" "pointerHashPolicy"])
                 (empty? (engine-field engine "taskRecords"))
                 (not (engine-field engine "graphInstalled")) (not (engine-field engine "moduleGraphInstalled"))
                 (empty? (engine-field engine "preparedGlobalSources")))
            "Abandonment requires stopped task-free execution without requests, imports or external protocol state")
      ;; Synchronous provider callbacks have returned when advancing is false
      ;; under this exclusive lease. No effect is replayed or retried.
      (heap-action-chain! (engine-field engine "runtimeAction") (:entropy-action requirements))
      (heap-action-chain! (engine-field engine "failedRuntimeAction") (:entropy-action requirements)))))
(defn- abandon!-in-lease [token]
  (let [cell (live-cell! token) {:keys [status prepared engine error-slot ledger module-index]} @cell]
    (need (#{:cancelled :host-failed :io-error :close-started} status) "Only terminal stopped computation can be abandoned")
    (heap-abandonable! prepared engine)
    (let [terminal {:status :abandoned :lock (:lock @cell)
                    :abandonment {:profile :task-free-captured-output-v1 :prior-status status
                                  :modules-entered (count ledger) :module-index module-index
                                  :guest-rc-unwound false :native-resource-finalization false
                                  :abandonment-invoked-engine-close false
                                  :prior-coordinator-close-attempted? (= :close-started status)
                                  :engine-disposed-claimed false}}]
      ;; Allocate the terminal record first. Clearing the journal and dropping
      ;; private references are host GC abandonment, not DEC/close/disposal.
      (when error-slot (aset ^objects error-slot 0 nil))
      (reset! cell terminal)
      (:abandonment terminal))))

;; One lock per startup/project world. No Java engine operation, callback or
;; live owner journal is shared across concurrent borrowers. Idle handoff is
;; permitted; entropy captures the current operation thread at effect entry.
(defn status [token] (with-lease! token :observe #(status-in-lease token)))
(defn owner-packet [token] (with-lease! token :observe #(owner-packet-in-lease token)))
(defn with-ready-engine! [token callback] (with-lease! token :invoke #(with-ready-engine!-in-lease token callback)))
(defn poll! [token budget]
  (need (and (integer? budget) (<= 1 budget 20000)) "Startup budget must be 1..20000")
  (with-lease! token :poll #(poll!-in-lease token budget)))
(defn cancel! [token] (with-lease! token :cancel #(cancel!-in-lease token)))
(defn release-error! [token] (with-lease! token :cleanup #(release-error!-in-lease token)))
(defn close! [token] (with-lease! token :cleanup #(close!-in-lease token)))
(defn abandon! [token] (with-lease! token :abandon #(abandon!-in-lease token)))
