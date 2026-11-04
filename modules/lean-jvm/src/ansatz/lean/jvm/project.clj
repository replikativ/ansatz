(ns ansatz.lean.jvm.project
  "Private issued Project leases behind the Java facade. No raw guest values,
   native producer receipts or mutable engine aliases cross that facade."
  (:require [ansatz.lean.jvm.ir :as ir] [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.publisher :as publisher] [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm.signature :as signature] [ansatz.lean.jvm.codec :as codec]
            [ansatz.lean.jvm.value :as value]
            [ansatz.lean.jvm.host :as host]
            [ansatz.lean.jvm.scalar-buffer :as scalar]
            [ansatz.lean.jvm.argument :as argument] [ansatz.lean.jvm.construction :as construction]
            [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.math BigInteger] [java.nio.charset StandardCharsets]
           [java.util WeakHashMap] [ansatz.lean.jvm MainResult IOResult LeanUnit LeanType InvocationOptions HostServices FileAccess HostBindings]))
(deftype Services [basis capability files startup-instructions startup-nanos])
(deftype Project [])
(deftype Handle [owner name signature types])
(defonce ^:private projects (WeakHashMap.))
;; Only an actual lifetime invariant refusal enters quarantine. It never counts
;; as successful cleanup; keep actual private custody instead of losing owners.
(defonce ^:private quarantine (atom []))
(def ^:private quarantine-limit 256)
(def ^:private default-startup-instructions InvocationOptions/DEFAULT_INSTRUCTIONS)
(def ^:private default-startup-nanos (.toNanos InvocationOptions/DEFAULT_TIME))
(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- cell! [project]
  (need (= Project (class project)) "RuntimeBoundary" "Actual Project issuer required")
  (locking projects (or (.get projects project) (throw (ex-info "Expired Project" {:code "RuntimeBoundary"})))))
(defn- live! [cell]
  (need (not= :failed (:status @cell)) "ProjectFailed"
        "An earlier call failed during execution; restart() the Project or load a new one")
  (need (= :ready (:status @cell)) "RuntimeBoundary" "Project is closed"))
(defn- typed-name [value]
  (need (and (string? value) (<= 1 (count value) 16384)) "EntryRejected" "Bounded dotted entry name required")
  (let [parts (str/split value #"\." -1)]
    (need (and (<= (count parts) 128) (every? #(<= 1 (count %) 4096) parts)) "EntryRejected" "Empty or excessive name segment")
    (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts)))
(defn- label [name]
  (loop [name name parts ()]
    (if (= name ["anonymous"]) (str/join "." parts)
        (recur (second name) (conj parts (nth name 2))))))
(defn- nat! [value]
  (need (and (= BigInteger (class value)) (not (neg? (.signum ^BigInteger value)))
             (<= (.bitLength ^BigInteger value) 4096)) "ResourceLimit" "Nat requires a nonnegative BigInteger of at most 4096 bits") value)
(defn- result-nat! [value]
  (nat! (if (= Long (class value)) (BigInteger/valueOf (long value)) value)))
(defn- string! [value]
  (need (and (= String (class value)) (<= (.length ^String value) 65536)
             (= value (String. (.getBytes ^String value StandardCharsets/UTF_8) StandardCharsets/UTF_8)))
        "ResourceLimit" "String requires valid Unicode and at most 65536 UTF-16 units") value)
(defn- invoke-zero [engine name]
  (.invoke (.getMethod (class engine) name (make-array Class 0)) engine (object-array 0)))
(defonce ^:private typed-methods
  (delay
    (let [bridge (Class/forName "ansatz.lean.jvm.ValueBridge")
          method (fn [name types] (doto (.getDeclaredMethod bridge name (into-array Class types)) (.setAccessible true)))]
      {:prepare (method "prepareValue" [LeanType Object String])
       :validate (method "validateArguments" [LeanType (class (object-array 0))])
       :export (method "exportValue" [LeanType Object String])})))
(defn- typed-call [operation arguments]
  (try (ir/invoke-static (get @typed-methods operation) arguments)
       (catch java.lang.reflect.InvocationTargetException failure
         (if (and (#{:prepare :validate} operation) (instance? IllegalArgumentException (.getCause failure)))
           (throw (ex-info (.getMessage ^Throwable (.getCause failure))
                           {:code (if (= :validate operation) "ResourceLimit" "InvalidArgument")} failure))
           (throw failure)))))
(defn- deadline! [engine nanos]
  (.invoke (.getMethod (class engine) "configureAtomicDeadlineAfterNanos" (into-array Class [Long/TYPE]))
           engine (object-array [(long nanos)])))
(defn- panic-policy! [engine fail?]
  (.invoke (.getMethod (class engine) "configurePanicPolicy" (into-array Class [Boolean/TYPE]))
           engine (object-array [(boolean fail?)])))
(defn- drain! [engine] (vec (invoke-zero engine "drainCapturedBytes")))
(defn- begin-invocation! [engine ^InvocationOptions options stdout-prefix stderr-prefix]
  (.invoke (.getMethod (class engine) "beginInvocation"
                       (into-array Class [(class (byte-array 0)) Integer/TYPE Integer/TYPE]))
           engine (object-array [(.stdinBytes options)
                                 (int (- (.stdoutLimitBytes options) stdout-prefix))
                                 (int (- (.stderrLimitBytes options) stderr-prefix))])))
(defn- join-bytes [^bytes prefix ^bytes suffix]
  (let [out (byte-array (+ (alength prefix) (alength suffix)))]
    (System/arraycopy prefix 0 out 0 (alength prefix))
    (System/arraycopy suffix 0 out (alength prefix) (alength suffix)) out))
(defn- codec-bytes []
  (let [resource (io/resource "META-INF/ansatz-lean-jvm/user-error.json")]
    (need resource "RuntimeBoundary" "SDK codec resource is absent")
    (with-open [input (io/input-stream resource)]
      (let [bytes (.readNBytes input 16385)]
        (need (<= (alength bytes) 16384) "RuntimeBoundary" "SDK codec resource exceeds bound") bytes))))
(defn- entropy [basis]
  (let [cls (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$EntropyCapability" true (:loader basis))]
    (ir/invoke-static (.getMethod cls "secureRandom" (into-array Class [String String Integer/TYPE]))
                      ["DRBG" "" (int 1048576)])))
(defn runtime-service!
  "One shared JDK DRBG service per Java Lean scope, initialized lazily."
  ([] (let [basis (ir/linked-basis)]
        (Services. basis (entropy basis) nil default-startup-instructions default-startup-nanos)))
  ([configuration]
   (need (= HostServices (class configuration)) "RuntimeBoundary" "Actual HostServices configuration required")
   (let [basis (ir/linked-basis) ^HostServices configuration configuration]
     (Services. basis (entropy basis) (.fileAccess configuration)
                (.startupInstructionBudget configuration) (.startupTimeBudgetNanos configuration)))))
(defn- startup-from-failure [failure]
  (loop [failure failure left 8]
    (when (and failure (pos? left))
      (or (when (instance? clojure.lang.IExceptionInfo failure) (:startup (ex-data failure)))
          (recur (.getCause ^Throwable failure) (dec left))))))
(defn- retire! [cell]
  (let [{:keys [run slot]} @cell
        failure
        (when run
          (try
            (let [status (:status (startup/status run))]
              (cond
                (#{:closed :abandoned} status) nil
                (#{:host-failed :close-started} status) (startup/abandon! run)
                (= :running status) (do (startup/cancel! run) (startup/abandon! run))
                (= :io-error status) (do (startup/release-error! run) (startup/close! run))
                :else (startup/close! run)))
            nil
            (catch Throwable failure
              (try (startup/abandon! run)
                   (catch Throwable refused
                     (swap! quarantine conj cell)
                     (throw failure)))
              ;; Preserve an actual normal-close failure even when the separately
              ;; certified host-reference abandonment subsequently succeeds.
              failure)))]
    (when slot (dotimes [i (alength ^objects slot)] (aset ^objects slot i nil)))
    (when (and (nil? run) (:files @cell)) (.close ^java.lang.AutoCloseable (:files @cell)))
    ;; Keep the verified prepared evidence so a retired Project can restart.
    (reset! cell (assoc (select-keys @cell [:services :prepared]) :status :closed))
    (when failure (throw failure))))
(defn- project-files [services prepared]
  (when (startup/filesystem-required? prepared)
    (let [files (.-files ^Services services)]
      (need (= FileAccess (class files)) "CapabilityMissing" "Project requires explicit filesystem services")
      (ir/file-session (.-basis ^Services services) files))))
(defn- start! [cell services prepared]
  ;; A fresh engine and filesystem session for already verified prepared evidence.
  (let [files (project-files services prepared)
        _ (swap! cell assoc :files files :slot (object-array 3))
        run (startup/open! prepared (.-capability ^Services services) files)
        instructions (long (.-startup-instructions ^Services services))
        nanos (long (.-startup-nanos ^Services services))]
    (swap! cell assoc :run run)
    (deadline! (:engine (startup/owner-packet run)) nanos)
    (let [deadline (+ (System/nanoTime) nanos)]
      (loop [left instructions]
        (when (.isInterrupted (Thread/currentThread))
          (throw (ex-info "Project startup interrupted" {:code "Cancelled"})))
        (need (and (pos? left) (< (System/nanoTime) deadline)) "ResourceLimit" "Project startup cooperative budget exhausted")
        (case (:status (startup/status run))
          :ready nil
          :running (do (startup/poll! run (min 128 left)) (recur (- left (min 128 left))))
          :io-error (throw (ex-info "Project initialization returned an IO error" {:code "InitializationFailed"}))
          (throw (ex-info "Project initialization stopped" {:code "InitializationFailed"})))))
    (let [[output types] (startup/with-ready-engine! run
                   (fn [{:keys [engine types]}]
                     (invoke-zero engine "clearAtomicDeadline")
                     [(drain! engine) types]))]
      (swap! cell assoc :status :ready :prefix output :types types))))
(defn- abandon-start! [cell failure]
  (when-not (:run @cell)
    (when-let [run (startup-from-failure failure)] (swap! cell assoc :run run)))
  (try (retire! cell) (catch Throwable _ nil)))
(defn- open-prepared! [services prepared]
  (need (< (count @quarantine) quarantine-limit) "RuntimeBoundary"
        "Too many Projects whose cleanup was refused are retained; restart the JVM")
  (let [cell (atom {:status :opening :services services :prepared prepared}) token (Project.)]
    (try
      (start! cell services prepared)
      (locking projects (.put projects token cell)) token
      (catch Throwable failure
        (abandon-start! cell failure)
        (throw failure)))))
(defn status!
  "Public Project state: \"ready\", \"failed\" or \"closed\"."
  [project]
  (let [cell (cell! project)]
    (locking cell
      (case (:status @cell) :ready "ready" :failed "failed" "closed"))))
(defn restart!
  "Retire the current engine and initialize a fresh one from the same verified
   prepared artifact. Function handles stay valid; globals and IO.Ref state are
   reinitialized. Allowed after a failed call or on a ready Project."
  [project]
  (let [cell (cell! project)]
    (locking cell
      (need (and (#{:ready :failed :closed} (:status @cell)) (not (:closed-by-owner @cell)) (:prepared @cell))
            "RuntimeBoundary" "Only an open Project can restart")
      (let [{:keys [services prepared]} @cell]
        (when-not (= :closed (:status @cell)) (retire! cell))
        (swap! cell assoc :status :opening)
        (try (start! cell services prepared)
             (catch Throwable failure (abandon-start! cell failure) (throw failure))))
      nil)))
(defn open-artifact!
  ([services input expected-manifest-sha] (open-artifact! services input expected-manifest-sha (HostBindings/empty)))
  ([services input expected-manifest-sha bindings]
  (let [receipt (artifact/load! input expected-manifest-sha) basis (.-basis ^Services services)]
    (open-prepared! services (publisher/prepare-artifact! basis receipt (codec-bytes) bindings)))))
(defn open-project!
  ([services source-root options] (open-project! services source-root options (HostBindings/empty)))
  ([services source-root options bindings]
  ;; Resolve and retire native services before any runtime Project is opened.
  (let [binding-names (host/binding-names bindings)
        requested (mapv (fn [entry] {:name (typed-name (.name entry)) :signature (.signature entry)}) (.entries options))
        _ (need (= (count requested) (count (set (map :name requested)))) "EntryRejected" "Duplicate requested entry name")
        bundle-open (requiring-resolve 'ansatz.lean.jvm.compiler.bundle/open!)
        build (requiring-resolve 'ansatz.lean.jvm.compiler.evidence/build!)
        compiler-close (requiring-resolve 'ansatz.lean.jvm.compiler.transport/close!)
        {:keys [compiler project-options evidence-options]} (bundle-open (.compiler options))
        receipt
        (try
          (let [configuration ((requiring-resolve 'ansatz.lean.jvm.compiler.bundle/source-configuration!) compiler project-options source-root options)
                roots (:roots configuration)
                entries (mapv #(assoc % :root (first roots)) requested)
                selected (set (map :name entries))
                entries (into entries (for [name binding-names :when (not (selected name))]
                                        {:root (first roots) :name name :signature "auto"}))
                _ (need (<= (count entries) 1024) "EntryRejected" "Combined entries and bindings exceed selection limit")]
            (build compiler configuration
                   evidence-options entries (atom {})))
          (finally (compiler-close compiler)))
        basis (.-basis ^Services services)]
    (open-prepared! services (publisher/prepare-build-bytes! basis receipt (codec-bytes) bindings)))))
(defn- descriptor [profile]
  (if (string? profile) (signature/from-legacy profile) (signature/validate! profile)))
(defn lookup-function! [project name requested-profile]
  (let [cell (cell! project) name (typed-name name)]
    (locking cell
      (live! cell)
      (let [[actual-signature callable? storage roots] (startup/with-ready-engine! (:run @cell)
                      (fn [{:keys [entries headers typed-groups]}]
                        (let [entry (first (filter #(= name (get % "name")) entries))]
                          [(get-in entry ["typeCheck" "signature"])
                           (some? (get headers (get-in entry ["callable" "name"]))) (get entry "typedStorage")
                           (when-let [storage (get entry "typedStorage")]
                             (get-in typed-groups [(get storage "group") :logical "roots"]))])))]
        ;; Ordinary requested-name/type rejection is outside the runtime callback.
        (need (and actual-signature callable?) (if requested-profile "EntryRejected" "EntryNotAdmitted")
              "No admitted checked entry matches this name; it may not have been exported")
        (need (or (nil? requested-profile)
                  (= (descriptor requested-profile)
                     (if storage
                       {"arguments" (mapv #(nth roots %) (get storage "arguments"))
                        "result" (nth roots (get storage "result")) "effect" (get storage "effect")}
                       (descriptor actual-signature)))) "EntryRejected"
              "Checked entry has another signature")
        (if storage
          (let [roots (nth (:types @cell) (get storage "group"))
                args (mapv #(nth roots %) (get storage "arguments"))
                result (nth roots (get storage "result"))]
            (Handle. project name (assoc actual-signature "schema" "lean-jvm-function/3")
                     {:arguments args :result result}))
          (Handle. project name (descriptor actual-signature) nil))))))
(defn- handle-signature! [project handle]
  (let [cell (cell! project)]
    (locking cell
      (live! cell)
      (need (and (= Handle (class handle)) (identical? project (.-owner ^Handle handle)))
            "EntryRejected" "Function handle belongs to another Project")
      (.-signature ^Handle handle))))
(defn function-descriptor! [project handle]
  (let [signature (handle-signature! project handle)]
    (if-let [types (.-types ^Handle handle)]
      (assoc signature "arguments" (:arguments types) "result" (:result types))
      signature)))
(defn function-type! [project handle]
  (let [descriptor (function-descriptor! project handle)]
    (if (= "lean-jvm-function/3" (get descriptor "schema")) "native-checked/3" (signature/display descriptor))))
(defn function-arity! [project handle] (count (get (function-descriptor! project handle) "arguments")))
(defn function-types! [project handle]
  (function-descriptor! project handle)
  (when-let [types (.-types ^Handle handle)]
    (java.util.List/of (:arguments types) (:result types))))
(defn- entry! [entries headers name expected-descriptor]
  (let [entry (first (filter #(= name (get % "name")) entries))]
    (need (= expected-descriptor (if (get entry "typedStorage")
                                  (assoc (get-in entry ["typeCheck" "signature"]) "schema" "lean-jvm-function/3")
                                  (descriptor (get-in entry ["typeCheck" "signature"])))) "EntryRejected" "Checked entry signature changed")
    [(get headers (get-in entry ["callable" "name"])) (label (get-in entry ["callable" "name"])) entry]))
(defn- drive! [ctx engine callable args slot host-calls ^InvocationOptions options]
  (deadline! engine (.timeBudgetNanos options))
  (let [deadline (+ (System/nanoTime) (.timeBudgetNanos options))
        instruction-limit (.instructionBudget options)]
    (aset ^objects slot 1 :start-pending)
    (ir/start! ctx engine callable args)
    ;; Successful owned call adopts the argument roots. A thrown start keeps
    ;; the actual journal and follows whole-branch abandonment, never guessed DEC.
    (aset ^objects slot 0 nil)
    (aset ^objects slot 1 :running)
    (loop []
      (when (.isInterrupted (Thread/currentThread)) (throw (ex-info "Project call interrupted" {:code "Cancelled"})))
      (need (< (System/nanoTime) deadline) "ResourceLimit" "Project call cooperative deadline exhausted")
      (case (ir/phase ctx engine)
        "complete" nil
        "host-call" (do (host/complete! ctx engine host-calls) (recur))
        "running" (let [left (- instruction-limit (ir/instructions ctx engine))]
                    (need (pos? left) "ResourceLimit" "Project call instruction budget exhausted")
                    (ir/advance! ctx engine (min 128 left)) (recur))
        (throw (ex-info "Unsupported runtime boundary" {:code "CapabilityMissing"}))))
    (need (identical? (aget ^objects slot 2)
                     (#'startup/engine-field (#'startup/engine-field engine "entry") "header"))
          "RuntimeBoundary" "Actual root callable Header changed")
    (aset ^objects slot 1 :take-pending)
    (let [value (ir/take-result! ctx engine)]
      (aset ^objects slot 0 value) (aset ^objects slot 1 :owned) value)))
(defn- finish-result! [ctx engine value slot]
  (aset ^objects slot 1 :release-started)
  (ir/release! ctx engine value)
  (aset ^objects slot 0 nil) (aset ^objects slot 1 :released) (aset ^objects slot 2 nil)
  (invoke-zero engine "clearAtomicDeadline")
  (drain! engine))
(defn- io-envelope! [ctx value]
  (need (= (:node-class ctx) (class value)) "RuntimeBoundary" "IO entry returned another carrier")
  (let [tag (.get ^java.lang.reflect.Field (:tag ctx) value)
        fields (.get ^java.lang.reflect.Field (:fields ctx) value)
        scalars (.get ^java.lang.reflect.Field (:scalars ctx) value)
        kind-method (.getDeclaredMethod ^Class (:class ctx) "kindMetadata" (into-array Class [(:node-class ctx)]))
        _ (.setAccessible kind-method true)]
    (need (and (= 1 (alength ^objects fields)) (zero? (alength ^bytes scalars)) (#{0 1} tag)
               (not (neg? (.get ^java.lang.reflect.Field (:rc ctx) value)))
               (every? #(false? (#'startup/engine-field value %)) ["dead" "array" "ref" "readyTask"])
               (nil? (#'startup/engine-field value "closure"))
               (nil? (.invoke kind-method nil (object-array [value]))))
          "RuntimeBoundary" "IO entry returned an unsupported result envelope")
    [tag (aget ^objects fields 0)]))
(defn- io-result! [ctx value]
  (let [[tag payload] (io-envelope! ctx value)]
    (if (= 0 tag)
      (do (need (and (= Long (class payload)) (zero? (long payload)))
                "RuntimeBoundary" "IO Unit entry returned another payload") :ok)
      :io-error)))
(defn- typed-io-result! [ctx type raw]
  ;; V3 normalization verified the actual EST.Out object0 + erased-world layout
  ;; and all IO.Error constructors before Project publication. Freeze the pure
  ;; success payload only; the owned envelope follows the ordinary release path.
  (let [[tag payload] (io-envelope! ctx raw)]
    (if (zero? tag)
      {:kind :ok :value (typed-call :export [type payload "object"])}
      {:kind :io-error :details (value/decode-io-error ctx payload)})))
(defn invoke-arguments-with-options! [project handle arguments options]
  (need (= InvocationOptions (class options)) "InvalidArgument" "Actual InvocationOptions required")
  (let [cell (cell! project)]
    (locking cell
      (live! cell)
      (let [descriptor (handle-signature! project handle)
            metadata (startup/with-ready-engine! (:run @cell)
                       (fn [{:keys [entries headers]}]
                         (nth (entry! entries headers (.-name ^Handle handle) descriptor) 2)))
            ;; Host input refusal happens before entering the execution lease.
            types (.-types ^Handle handle)
            _ (when types (need (= (count (:arguments types)) (count arguments)) "ArityMismatch" "Wrong explicit argument count"))
            planned (if types
                      {:constructors []
                       :roots (mapv (fn [type host param]
                                      (typed-call :prepare [type host (get param "ty")]))
                                    (:arguments types) arguments (get-in metadata ["callable" "xs"]))}
                      (argument/plan descriptor (get metadata "codecWitnesses") arguments))
            io? (= "io" (get descriptor "effect"))
            planned (cond-> planned io? (update :roots conj (long 0)))
            _ (when types (typed-call :validate [(:result types) (object-array (:roots planned))]))
            slot (:slot @cell)
            ^InvocationOptions options options
            [prefix-out prefix-err] (:prefix @cell)
            stdout-prefix (if io? (alength ^bytes prefix-out) 0)
            stderr-prefix (if io? (alength ^bytes prefix-err) 0)]
        ;; A tighter policy may refuse pending initialization output without
        ;; entering a guest lease or poisoning a healthy Project.
        (need (and (<= stdout-prefix (.stdoutLimitBytes options))
                   (<= stderr-prefix (.stderrLimitBytes options)))
              "ResourceLimit" "Initialization output exceeds invocation limits")
        ;; Once the engine has returned, released the result and ended the
        ;; invocation it is idle and consistent: later refusals (a returned IO
        ;; error, unexpected pure output) leave the Project ready. A failure
        ;; inside execution leaves guest state unknown and retires it.
        (let [completed (volatile! false)]
        (try
          (let [{:keys [decoded output]}
                (startup/with-ready-engine! (:run @cell)
                  (fn [{:keys [ctx engine entries headers host-calls]}]
                    (let [[header callable entry] (entry! entries headers (.-name ^Handle handle) descriptor)
                          _ (need (some? header) "RuntimeBoundary" "Actual callable Header absent")
                          _ (panic-policy! engine (.failOnPanic options))
                          _ (begin-invocation! engine options stdout-prefix stderr-prefix)
                          _ (aset ^objects slot 2 header)
                          runtime-arguments (construction/materialize! ctx engine planned)
                          _ (aset ^objects slot 0 runtime-arguments)
                          _ (aset ^objects slot 1 :constructed)
                          raw (drive! ctx engine callable runtime-arguments slot host-calls options)
                          decoded
                          (if types
                            (if io? (typed-io-result! ctx (:result types) raw)
                              (typed-call :export [(:result types) raw (get-in entry ["callable" "type"])]))
                            (if io?
                            (if (string? (get-in entry ["typeCheck" "signature"]))
                              ;; Legacy IO Unit has the independently pinned SDK codec
                              ;; witness; v2 must use its actual compiler layout evidence.
                              (let [kind (io-result! ctx raw)]
                                {:kind kind :value LeanUnit/INSTANCE
                                 :details (when (= :io-error kind)
                                            (value/decode-io-error ctx (aget ^objects (.get ^java.lang.reflect.Field (:fields ctx) raw) 0)))})
                              (value/decode-io ctx entry raw))
                            (if (= "raw-nullary-scalar" (get entry "resultABI"))
                              (scalar/decode-external-scalar (get descriptor "result") raw)
                              (value/decode ctx (get descriptor "result") (get entry "codecWitnesses") raw))))
                          output (finish-result! ctx engine raw slot)
                          _ (invoke-zero engine "endInvocation")]
                      {:decoded decoded :output output})))
                _ (vreset! completed true)]
            (if io?
              (do
                (when-not (= :ok (:kind decoded))
                  (throw (ex-info "Lean IO entry returned an error"
                                  {:code "GuestIOError" :guest-io-error (:details decoded)})))
                (let [[out err] output]
                  (swap! cell assoc :prefix [(byte-array 0) (byte-array 0)])
                  (IOResult. (:value decoded) (join-bytes prefix-out out) (join-bytes prefix-err err))))
              (let [[^bytes out ^bytes err] output]
                (need (zero? (alength out)) "RuntimeBoundary" "Pure checked entry produced captured stdout")
                ;; As in native Lean, a pure function's panic messages reach the
                ;; process stderr; IO entries return them in IOResult.stderr.
                (when (pos? (alength err)) (.write System/err err 0 (alength err)) (.flush System/err))
                decoded)))
          (catch Throwable failure
            (when-not @completed (swap! cell assoc :status :failed))
            (throw failure))))))))
(defn invoke-arguments! [project handle arguments]
  (invoke-arguments-with-options! project handle arguments (InvocationOptions/empty)))
(defn invoke-function! [project handle input]
  (let [descriptor (handle-signature! project handle)]
    (need (if-let [types (.-types ^Handle handle)]
            (and (= "pure" (get descriptor "effect")) (= 1 (count (:arguments types)))
                 (= (.kind ^LeanType (first (:arguments types))) (.kind ^LeanType (:result types)))
                 (contains? #{ansatz.lean.jvm.LeanType$Kind/NAT ansatz.lean.jvm.LeanType$Kind/STRING} (.kind ^LeanType (:result types))))
            (contains? #{(signature/from-legacy "nat-to-nat") (signature/from-legacy "string-to-string")} descriptor))
          "EntryRejected" "Typed unary convenience requires its checked unary profile")
    (invoke-arguments! project handle (object-array [input]))))
(defn run-main! [project]
  (let [cell (cell! project)]
    (locking cell
      (live! cell)
      (let [io-unit (signature/from-legacy "io-unit")
            mains (startup/with-ready-engine! (:run @cell)
                    (fn [{:keys [entries]}]
                      (filterv (fn [entry]
                                 (if-let [storage (get entry "typedStorage")]
                                   (and (= "io" (get storage "effect")) (empty? (get storage "arguments"))
                                        (= ansatz.lean.jvm.LeanType$Kind/UNIT (.kind ^LeanType (nth (nth (:types @cell) (get storage "group")) (get storage "result")))))
                                   (= io-unit (descriptor (get-in entry ["typeCheck" "signature"]))))) entries)))]
        (need (= 1 (count mains)) "EntryRejected" "Exactly one checked IO Unit entry is required")
        (let [handle (lookup-function! project (label (get (first mains) "name")) nil)
              ^IOResult result (invoke-arguments! project handle (object-array 0))]
          (MainResult. (.stdout result) (.stderr result)))))))
(defn close! [project]
  (let [cell (cell! project)]
    (locking cell
      (try
        (when-not (= :closed (:status @cell))
          (swap! cell assoc :status :closing)
          (retire! cell))
        ;; Drop the prepared evidence; a quarantined cell keeps its custody.
        (finally (if (= :closed (:status @cell))
                   (reset! cell {:status :closed :closed-by-owner true})
                   (swap! cell assoc :closed-by-owner true))))) nil))
