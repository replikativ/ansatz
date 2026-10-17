(ns prototype.hosted-file
  "Small file runner over an explicitly prepared hosted Lean session. Bootstrap,
   imports, linked helpers and capabilities are caller responsibilities. No native
   per-input compiler, environment rewriting, inferred imports or publication."
  (:require [prototype.frontend :as frontend]
            [prototype.guest-encoding :as encoding]
            [prototype.eval-const :as eval]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.source-module :as source-module])
  (:import [ansatz.kernel Name]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- structured-name [^Name name]
  (when-not (instance? Name name) (fail "Hosted file names must be kernel Names" {}))
  (loop [name name parts []]
    (if (.isAnonymous name)
      (reduce (fn [prefix [kind value]] [kind prefix value]) ["anonymous"] (rseq parts))
      (recur (.-prefix name) (conj parts (if (.isStr name) ["str" (.-str name)] ["num" (str (.-num name))]))))))

(defn- source [{:keys [path text file-name] :as request}]
  (when-not (not= (contains? request :path) (contains? request :text))
    (fail "Supply exactly one hosted file :path or :text" {}))
  (when (and (contains? request :path) (not (and (string? path) (seq path)))) (fail "Invalid hosted file path" {}))
  (let [filename (or file-name path)]
    (when-not (and (string? filename) (seq filename)) (fail "Hosted file requires a file name" {}))
    (when (and (contains? request :text) (not (string? text))) (fail "Hosted file text must be a string" {}))
    {:text (if (contains? request :path) (slurp path :encoding "UTF-8") text) :file-name filename}))

(defn- invocation [session-atom]
  (fn [world target args]
    (let [result (raw/call @session-atom world target args)]
      (reset! session-atom (:session result))
      [(:state result) (:value result)])))

(defn- execution-request [request]
  (let [{:keys [module-name roots initialization calls]} request
         _ (when-not (contains? #{:defer :run} initialization)
             (fail "Hosted file requires explicit :initialization :defer or :run" {}))
         _ (structured-name module-name)
         _ (when-not (vector? roots) (fail "Hosted file roots must be a vector" {}))
         _ (doseq [name roots] (structured-name name))
         calls (or calls [])
         _ (when-not (vector? calls) (fail "Hosted file calls must be a vector" {}))
         calls (mapv (fn [{:keys [name args] :as call}]
                       (when-not (and (map? call) (vector? args)) (fail "Invalid hosted file call" {}))
                       (assoc call :structured-name (structured-name name))) calls)]
    {:module-name module-name :roots roots :initialization initialization :calls calls}))

(defn finish-file
  "Run the explicit initialization/call phase of an already compiled result.
   REQUEST has the same module/roots/initialization/calls contract as run-file.
   This never reads source, compiles, imports, or retries an operation. Returned
   values remain owned; errors retain completed calls and the latest checkpoint."
  [compiled request]
  (when-not (and (boolean? (:success compiled))
                 (map? (get-in compiled [:world :functions]))
                 (identical? (get-in compiled [:world :functions]) (get-in compiled [:session :functions])))
    (fail "Expected frontend compilation result with matching session" {}))
  (let [{:keys [initialization calls]} (execution-request request)]
     (if-not (:success compiled)
       (assoc compiled :call-results [] :initialization-state :not-compiled)
       (let [active (atom (:session compiled)) invoke (invocation active)
             results (volatile! []) progress (volatile! (:world compiled))]
         (try
           (let [digest (get-in compiled [:handle :unit-digest])
                 unit (get-in (:world compiled) [:eval-const-authorizations :units digest])
                 installation {:unit-digest digest :initialization-plan (get-in unit [:manifest :initializationPlan])}
                 world (if (= :run initialization)
                         (eval/run-initializers {:invoke invoke} (:world compiled) installation)
                         (:world compiled))
                 _ (vreset! progress world)
                 _ (when (and (seq calls) (= :defer initialization) (seq (:pending-local-initializers compiled)))
                     (fail "Hosted calls require running pending module initializers" {}))
                 world (reduce (fn [world {:keys [name args structured-name]}]
                                 (let [target (or (get (:boxed-entrypoints compiled) structured-name)
                                                  (fail "Hosted call is not an admitted boxed entrypoint" {:name structured-name}))
                                       [world value] (invoke world target args)]
                                   (vswap! results conj {:name name :target target :value value})
                                   (vreset! progress world)
                                   world)) world calls)]
             (assoc compiled :world world :session @active :call-results @results
                             :initialization-state (if (= :run initialization) :ready :deferred)
                             :pending-local-initializers (if (= :run initialization) [] (:pending-local-initializers compiled))))
           (catch Throwable cause
             (throw (ex-info (or (.getMessage cause) "Hosted file execution failed")
                             (merge {:checkpoint @progress}
                                    (ex-data cause)
                                    {:session (or (:session (ex-data cause)) (:checkpoint-session (ex-data cause)) @active)
                                     :compiled-environment (:environment compiled) :call-results @results}) cause))))))))

(defn run-file
  "PREPARED supplies :session/:world/:catalogue and borrowed guest :environment
   and :options. REQUEST supplies :module-name (kernel Name), :roots (vector of
   kernel Names), exactly one :path or :text (with :file-name), and REQUIRED
   :initialization :defer or :run. Optional :calls is [{:name kernel-Name :args
   raw-owned-arguments-vector} ...], resolved only through admitted boxed entries.

   Returns frontend's result with updated world/session and owned :call-results.
   Returned :environment remains owned, even on command diagnostics. Inputs stay
   borrowed; call arguments transfer only when their call actually starts. Raw
   results remain caller-owned until explicitly released. Calls with deferred
   pending module initializers are rejected. :run uses the admitted unit's actual
   guest initializer plan; it does not replay source-time registrations.

   CONFIGURATION follows frontend/compile-file; real guest encoders are defaults.
   The prepared catalogue always supplies installation backing. Errors preserve
   the latest checkpoint, active session, compiled environment and completed call
   results where available. They never authorize retrying external effects."
  ([prepared request] (run-file prepared request {}))
  ([{:keys [session world catalogue environment options]} request configuration]
   (when-not (map? catalogue) (fail "Hosted file requires an explicit prepared catalogue" {}))
   (let [{:keys [module-name roots]} (execution-request request)
         arguments (merge (source request) {:environment environment :options options :module-name module-name :roots roots})
         configuration (-> (merge {:encode-name encoding/encode-name :encode-names encoding/encode-names} configuration)
                           (assoc-in [:install-options :catalogue] catalogue))
         compiled (frontend/compile-file session world arguments configuration)]
     (finish-file compiled request))))

(defn export-module
  "Export an actual compiled Environment through already-linked guest helpers.
   PREPARED supplies :session/:world/:environment; MODULE is a kernel Name.
   Returns source-module/export-classic's owned result plus the adopted session.
   No disk write, module installation, publication or initialization occurs."
  ([prepared module] (export-module prepared module {}))
  ([{:keys [session world environment]} module configuration]
   (structured-name module)
   (let [active (atom session) invoke (invocation active)
         [world name] (encoding/encode-name world invoke module (:encoder-options configuration))]
     (try
       (let [result (source-module/export-classic world invoke environment name (:export-options configuration))]
         (assoc (update result :world m/release name 1) :session @active))
       (catch Throwable cause
         (throw (ex-info (or (.getMessage cause) "Hosted module export failed")
                         (merge (ex-data cause)
                                {:session (or (:session (ex-data cause)) (:checkpoint-session (ex-data cause)) @active)
                                 :hosted-file-temporary-owners [name]}) cause)))))))
