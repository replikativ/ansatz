(ns ansatz.lean.jvm
  "Clojure REPL interface to checked Lean project execution. Core Ansatz can be
   used alongside this optional module; kernel declaration import is separate."
  (:require [clojure.java.io :as io]
            [ansatz.lean.jvm.typed-value :as typed])
  (:import [ansatz.lean.jvm Lean LeanProject LeanFunction LeanPreparation PreparedArtifact
            NativeCompilerOptions ProjectOptions LeanUnit IOResult LeanChoice InvocationOptions HostServices HostBindings]
           [java.nio.file Path] [java.util Optional]))

(defn- path [value]
  (if (instance? Path value) value (.toPath (io/file value))))

(defn open
  ([] (Lean/open))
  ([services]
   (when-not (instance? HostServices services)
     (throw (ex-info "Actual HostServices configuration required" {:code "UnsupportedProjectConfig"})))
   (Lean/open ^HostServices services)))

(defn project-options
  "Explicit compiler configuration and requested entry names. A vector of names
   uses native signature discovery; a map can request legacy checked profiles."
  [{:keys [compiler root-module source-root entries installed-imports built-lake-workspace?]
    :or {root-module "Main" source-root "."}}]
  (let [native (NativeCompilerOptions. (path (:sysroot compiler))
                                      (path (:producer-bundle compiler)) (path (:cache compiler)))
        builder (-> (ProjectOptions/builder native) (.rootModule root-module) (.sourceRoot source-root))]
    (when (some? built-lake-workspace?)
      (when-not (boolean? built-lake-workspace?) (throw (IllegalArgumentException. "built-lake-workspace? must be Boolean")))
      (when built-lake-workspace? (.builtLakeWorkspace builder)))
    (when (some? installed-imports)
      (when-not (and (vector? installed-imports) (<= (count installed-imports) ProjectOptions/MAX_INSTALLED_IMPORTS)
                     (every? string? installed-imports) (= (count installed-imports) (count (set installed-imports))))
        (throw (ex-info "Installed imports must be a bounded vector of distinct exact module names"
                        {:code "UnsupportedProjectConfig"})))
      (doseq [module installed-imports] (.installedImport builder module)))
    (when-not (<= 1 (bounded-count (inc ProjectOptions/MAX_SELECTED_ENTRIES) entries) ProjectOptions/MAX_SELECTED_ENTRIES)
      (throw (ex-info "Request one to 1024 checked entries" {:code "EntryRejected"})))
    (doseq [[name signature] (if (map? entries) entries (map #(vector % :auto) entries))]
      (case signature
        :auto (.function builder name)
        :nat-to-nat (.natFunction builder name)
        :string-to-string (.stringFunction builder name)
        :io-unit (.main builder name)
        (throw (ex-info "No native checked export profile supports this signature yet"
                        {:code "UnsupportedSignature"}))))
    (.build builder)))

(defn bindings
  "Capture implementations by Lean declaration name. Supply :implementation-id,
   either :fn or :factory, and optionally :effect (:pure by default, or :io).
   A factory receives detached :argument-types and :result-type once at linking."
  [registrations]
  (if (= HostBindings (class registrations)) registrations
    (do
      (when-not (and (map? registrations) (<= (count registrations) HostBindings/MAX_BINDINGS))
        (throw (IllegalArgumentException. "Expected a bounded binding map")))
      (let [builder (HostBindings/builder)]
        (doseq [[name registration] registrations]
          (let [effect (get registration :effect :pure)
                factory? (contains? registration :factory)
                allowed (cond-> #{:implementation-id (if factory? :factory :fn)}
                          (contains? registration :effect) (conj :effect))]
            (when-not (and (string? name) (map? registration) (= allowed (set (keys registration)))
                           (#{:pure :io} effect))
              (throw (IllegalArgumentException. "Binding requires implementation-id, fn or factory, and pure/io effect")))
            (case [effect factory?]
              [:pure false] (.pureClojure builder name (:implementation-id registration) (:fn registration))
              [:pure true] (.pureClojureFactory builder name (:implementation-id registration) (:factory registration))
              [:io false] (.ioClojure builder name (:implementation-id registration) (:fn registration))
              [:io true] (.ioClojureFactory builder name (:implementation-id registration) (:factory registration)))))
        (.build builder)))))

(defn load-project
  "Load trusted source using explicit compiler options, passed as a map or a
   ProjectOptions object. No native installation or download is implicit."
  ([^Lean runtime directory options]
   (load-project runtime directory options (HostBindings/empty)))
  ([^Lean runtime directory options implementations]
   (.loadProject runtime (path directory)
                 (if (instance? ProjectOptions options) options (project-options options)) (bindings implementations))))

(defn prepare-project
  "Compile trusted source into OUTPUT without opening a JVM Project. Caller owns
   OUTPUT; keep the returned manifest hash separately in trusted configuration."
  [directory options output]
  (let [^PreparedArtifact description
        (LeanPreparation/prepareProject (path directory)
          (if (instance? ProjectOptions options) options (project-options options)) output)]
    {:manifest-sha256 (.manifestSHA256 description) :archive-sha256 (.archiveSHA256 description)}))

(defn load-artifact
  "The caller owns INPUT. EXPECTED-MANIFEST-SHA comes from a trusted descriptor."
  ([^Lean runtime input expected-manifest-sha]
   (load-artifact runtime input expected-manifest-sha (HostBindings/empty)))
  ([^Lean runtime input expected-manifest-sha implementations]
   (.loadArtifact runtime ^java.io.InputStream input ^String expected-manifest-sha (bindings implementations))))

(defn- clojure-value [type value]
  (case (get type "kind")
    "unit" nil
    "product" [(clojure-value (get type "first") (nth value 0))
               (clojure-value (get type "second") (nth value 1))]
    "option" (when (.isPresent ^Optional value)
               {:some (clojure-value (get type "element") (.get ^Optional value))})
    ("list" "array") (mapv #(clojure-value (get type "element") %) value)
    ("sum" "except") (let [left? (.isLeft ^LeanChoice value)
                              sum? (= "sum" (get type "kind"))
                              key (if sum? (if left? :left :right) (if left? :error :ok))
                              child (get type (if sum? (if left? "left" "right") (if left? "error" "value")))]
                          {key (clojure-value child (.value ^LeanChoice value))})
    value))

(defn- host-arguments [descriptor arguments]
  (let [remaining (volatile! 100000)]
    (letfn [(visit [type value depth]
              (when (.isInterrupted (Thread/currentThread))
                (throw (ex-info "Argument conversion cancelled" {:code "Cancelled"})))
              (when-not (and (< depth 128) (not (neg? (vswap! remaining dec))))
                (throw (ex-info "Argument conversion exceeds budget" {:code "ResourceLimit"})))
              (case (get type "kind")
                "unit" (if (nil? value) LeanUnit/INSTANCE value)
                "option" (cond
                           (nil? value) (Optional/empty)
                           (and (map? value) (= #{:some} (set (keys value))))
                           (Optional/of (visit (get type "element") (:some value) (inc depth)))
                           (= Optional (class value))
                           (if (.isPresent ^Optional value)
                             (Optional/of (visit (get type "element") (.get ^Optional value) (inc depth))) value)
                           :else (throw (ex-info "Option expects nil or {:some value}" {:code "UnsupportedArgumentType"})))
                ("sum" "except")
                (let [[left right] (if (= "sum" (get type "kind")) [:left :right] [:error :ok])
                      [left-type right-type] (if (= "sum" (get type "kind")) ["left" "right"] ["error" "value"])]
                  (cond
                    (and (map? value) (= #{left} (set (keys value))))
                    (LeanChoice/left (visit (get type left-type) (get value left) (inc depth)))
                    (and (map? value) (= #{right} (set (keys value))))
                    (LeanChoice/right (visit (get type right-type) (get value right) (inc depth)))
                    (= LeanChoice (class value))
                    (if (.isLeft ^LeanChoice value)
                      (LeanChoice/left (visit (get type left-type) (.value ^LeanChoice value) (inc depth)))
                      (LeanChoice/right (visit (get type right-type) (.value ^LeanChoice value) (inc depth))))
                    :else (throw (ex-info "Expected an explicitly tagged branch" {:code "UnsupportedArgumentType"}))))
                ("product" "list" "array")
                (do (when-not (and (instance? java.util.List value) (not (instance? clojure.lang.ISeq value)))
                      (throw (ex-info "Expected a bounded vector or java.util.List" {:code "UnsupportedArgumentType"})))
                    (let [size (.size ^java.util.List value) product? (= "product" (get type "kind"))]
                      (when-not (and (<= 0 size @remaining) (or (not product?) (= size 2)))
                        (throw (ex-info "Invalid container extent" {:code "InvalidArgument"})))
                      (mapv (fn [index]
                              (visit (if product? (get type (if (zero? index) "first" "second")) (get type "element"))
                                     (.get ^java.util.List value index) (inc depth))) (range size))))
                value))]
      (mapv #(visit %1 %2 0) (get descriptor "arguments") arguments))))

(defn invocation-options
  "Immutable per-call options: finite :stdin text or :stdin-bytes (mutually
   exclusive), :stdout-limit-bytes/:stderr-limit-bytes, the cooperative budget
   :instruction-budget and :time-budget-ms (defaults 2,000,000 and 5,000), and
   :fail-on-panic? (default false: panic! prints to stderr and continues with the
   default value, as native Lean does). Invalid options are rejected before
   guest execution."
  [options]
  (if (= InvocationOptions (class options)) options
    (do
      (when-not (and (map? options)
                     (every? #{:stdin :stdin-bytes :stdout-limit-bytes :stderr-limit-bytes
                               :instruction-budget :time-budget-ms :fail-on-panic?} (keys options))
                     (not (and (contains? options :stdin) (contains? options :stdin-bytes))))
        (throw (ex-info "Invalid invocation option keys or overlapping stdin forms" {:code "InvalidArgument"})))
      (let [^InvocationOptions native
            (cond
              (contains? options :stdin)
              (do (when-not (string? (:stdin options))
                    (throw (ex-info "stdin expects text" {:code "InvalidArgument"})))
                  (InvocationOptions/stdinText (:stdin options)))
              (contains? options :stdin-bytes)
              (do (when-not (= (class (byte-array 0)) (class (:stdin-bytes options)))
                    (throw (ex-info "stdin-bytes expects a byte array" {:code "InvalidArgument"})))
                  (InvocationOptions/stdinBytes (:stdin-bytes options)))
              :else (InvocationOptions/empty))
            out (get options :stdout-limit-bytes InvocationOptions/MAX_OUTPUT_BYTES)
            err (get options :stderr-limit-bytes InvocationOptions/MAX_OUTPUT_BYTES)]
        (when-not (every? #(and (integer? %) (<= 0 % InvocationOptions/MAX_OUTPUT_BYTES)) [out err])
          (throw (ex-info "Invalid output byte limit" {:code "InvalidArgument"})))
        (let [instructions (get options :instruction-budget InvocationOptions/DEFAULT_INSTRUCTIONS)
              millis (get options :time-budget-ms (.toMillis InvocationOptions/DEFAULT_TIME))
              panic? (get options :fail-on-panic? false)]
          (when-not (and (integer? instructions) (integer? millis) (boolean? panic?))
            (throw (ex-info "Budgets are integers and :fail-on-panic? is a boolean" {:code "InvalidArgument"})))
          (try
            (-> (.withOutputLimits native (int out) (int err))
                (.withBudget (long instructions) (java.time.Duration/ofMillis (long millis)))
                (.withFailOnPanic (boolean panic?)))
            (catch IllegalArgumentException invalid
              (throw (ex-info (.getMessage invalid) {:code "InvalidArgument"} invalid)))))))))

(defn- function*
  "Resolve an admitted checked function as an IFn bound to this Project. Exact
   integers, Boolean and strings retain ordinary Clojure carriers. Unit is nil;
   decoded products/lists are vectors, Option is nil or {:some value}. IO returns
   {:value value :stdout text :stderr text}. Unsupported codecs throw explicitly."
  [^LeanProject project name options]
  (let [^LeanFunction handle (.function project name)
        arity (.arity handle) descriptor (.descriptor handle)
        typed? (.hasTypeMetadata handle)
        argument-types (when typed? (.argumentTypes handle))
        result-type (when typed? (.resultType handle))]
    (with-meta
      (fn [& arguments]
        (when-not (= arity (bounded-count (inc arity) arguments))
          (throw (ex-info (str "Expected " arity " explicit arguments") {:code "ArityMismatch"})))
        (let [arguments (if typed? (mapv typed/host-value argument-types arguments)
                                  (host-arguments descriptor arguments))
              result (if options (.invokeWith handle ^InvocationOptions options (object-array arguments))
                         (.invoke handle (object-array arguments)))]
          (if (= "io" (get descriptor "effect"))
            (let [^IOResult result result]
              (cond-> {:value (if typed? (typed/view result-type (.value result))
                                 (clojure-value (get descriptor "result") (.value result)))
                       :stdout (.stdout result) :stderr (.stderr result)}
                options (assoc :stdout-bytes (.stdoutBytes result) :stderr-bytes (.stderrBytes result))))
            (if typed? (typed/view result-type result) (clojure-value (get descriptor "result") result)))))
      (cond-> {:lean/name name :lean/signature descriptor :lean/type (.signature handle) :lean/arity arity}
        typed? (assoc :lean/argument-types argument-types :lean/result-type result-type)))))

(defn materialize
  "Explicitly copy a detached typed view into ordinary Clojure maps/vectors.
   Immutable LeanBytes values become fresh byte arrays."
  [value] (typed/materialize value))

(defn function
  "Retain a callable. With invocation options, each call starts fresh finite
   stdin; IO results additionally include defensive stdout/stderr byte arrays."
  ([project name] (function* project name nil))
  ([project name options] (function* project name (invocation-options options))))

(defn call [project name & arguments]
  (apply (function project name) arguments))

(defn call-with-options [project name options & arguments]
  (apply (function project name options) arguments))

(defn run-main [^LeanProject project] (.runMain project))
(defn failed?
  "True after a call failed during execution; later calls are refused until restart!."
  [^LeanProject project] (.isFailed project))
(defn restart!
  "Reinitialize the Project from its verified artifact; function handles stay valid."
  [^LeanProject project] (.restart project) project)
(defn close! [^java.lang.AutoCloseable value] (.close value))
