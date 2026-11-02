(ns ansatz.lean.jvm.preparation
  "Trusted native source→portable artifact preparation. Never opens a JVM Project
   or invokes its runtime initializers/main; native compilation can execute metaprograms."
  (:require [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.compiler.bundle :as bundle]
            [ansatz.lean.jvm.compiler.evidence :as evidence]
            [ansatz.lean.jvm.compiler.transport :as transport]
            [clojure.data.json :as json] [clojure.string :as str])
  (:import [ansatz.lean.jvm LeanPreparation LeanException NativeCompilerOptions ProjectOptions]
           [java.io OutputStream]
           [java.nio.file Path Files LinkOption OpenOption StandardOpenOption]
           [java.nio.file.attribute FileAttribute]))

(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- typed-name [value]
  (need (and (= String (class value)) (<= 1 (count value) 16384)) "EntryRejected" "Bounded dotted entry name required")
  (let [parts (str/split value #"\." -1)]
    (need (and (<= (count parts) 128) (every? #(<= 1 (count %) 4096) parts)) "EntryRejected" "Empty or excessive name segment")
    (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts)))
(defn- failure-priority [failure]
  (cond (or (instance? VirtualMachineError failure) (instance? ThreadDeath failure)) 3
        (instance? Error failure) 2 :else 1))
(defn- with-cleanup [body cleanup]
  ;; Preserve an original error over ordinary cleanup failures without attaching
  ;; suppressed causes or mutating a Throwable that may retain private custody.
  (let [result (try {:value (body)} (catch Throwable error {:failure error}))
        closing (try (cleanup) nil (catch Throwable error error))
        original (:failure result)
        failure (if (and closing (or (nil? original) (> (failure-priority closing) (failure-priority original))))
                  closing original)]
    (if failure (throw failure) (:value result))))
(defn prepare!
  "Internal facade seam. Return only manifest/archive digest values. Caller owns
   OUTPUT, including failed writes; a failed export may leave partial bytes."
  [source-root options output]
  (need (instance? Path source-root) "UnsupportedProjectConfig" "Source directory must be a Path")
  (need (= ProjectOptions (class options)) "UnsupportedProjectConfig" "Explicit ProjectOptions required")
  (need (instance? OutputStream output) "UnsupportedArgumentType" "Artifact OutputStream required")
  (let [root (typed-name (.rootModule ^ProjectOptions options))
        entries (mapv (fn [entry] {:root root :name (typed-name (.name entry)) :signature (.signature entry)})
                      (.entries ^ProjectOptions options))]
    (need (= (count entries) (count (set (map :name entries)))) "EntryRejected" "Duplicate requested entry name")
    (let [{:keys [compiler project-options evidence-options]} (bundle/open! (.compiler ^ProjectOptions options))]
      (with-cleanup
        (fn []
          (let [receipt (evidence/build! compiler
                          (assoc project-options :project source-root :source-root (.sourceRoot ^ProjectOptions options) :roots [root])
                          evidence-options entries (atom {}))
                exported (artifact/export! receipt output)]
            ;; Receipt identity and source custody stay private and live through
            ;; export validation. Never prepare a Program or issue a Project here.
            (select-keys exported [:manifest-sha256 :archive-sha256])))
        #(transport/close! compiler)))))

(def ^:private usage
  (str "Prepare a Lean JVM artifact without opening a JVM Project.\n"
       "--source DIR --sysroot DIR --producer-bundle DIR --cache DIR --output FILE\n"
       "[--source-root RELATIVE-DIR] [--root-module NAME]\n"
       "--entry NAME (repeat for native signature discovery), or\n"
       "--nat-function NAME | --string-function NAME | --main NAME\n"
       "Output must not exist. Native frontend execution is trusted; no implicit install.\n"))
(def ^:private single-flags
  {"--source" :source "--sysroot" :sysroot "--producer-bundle" :producer-bundle
   "--cache" :cache "--output" :output "--source-root" :source-root "--root-module" :root-module})
(def ^:private entry-flags
  {"--entry" :auto "--nat-function" :nat-to-nat "--string-function" :string-to-string "--main" :io-unit})
(defn- parse-cli [arguments]
  (let [maximum (+ 32 (* 2 ProjectOptions/MAX_SELECTED_ENTRIES))]
    (need (<= (bounded-count (inc maximum) arguments) maximum) "InvalidArguments" "Too many command-line arguments")
    (let [arguments (vec arguments)]
      (need (every? #(and (= String (class %)) (<= 1 (count %) 16384)) arguments)
            "InvalidArguments" "Expected bounded nonempty command-line strings")
      (if (= ["--help"] arguments) {:help true}
        (loop [remaining arguments parsed {:entries []}]
          (if (empty? remaining)
            (do (need (every? #(contains? parsed %) [:source :sysroot :producer-bundle :cache :output])
                      "InvalidArguments" "Missing required preparation option; use --help")
                (need (seq (:entries parsed)) "InvalidArguments" "Request at least one entry") parsed)
            (let [[flag value & tail] remaining]
              (need (and value (not (str/starts-with? value "--"))) "InvalidArguments" "Every preparation option requires a value")
              (cond
                (contains? single-flags flag)
                (let [key (get single-flags flag)]
                  (need (not (contains? parsed key)) "InvalidArguments" "Duplicate preparation option")
                  (recur tail (assoc parsed key value)))
                (contains? entry-flags flag)
                (do (need (< (count (:entries parsed)) ProjectOptions/MAX_SELECTED_ENTRIES)
                          "EntryRejected" "Too many selected entries")
                    (recur tail (update parsed :entries conj [value (get entry-flags flag)])))
                :else (throw (ex-info "Unknown preparation option; use --help" {:code "InvalidArguments"}))))))))))
(defn- path [value] (Path/of ^String value (make-array String 0)))
(defn- cli-options [parsed]
  (let [compiler (NativeCompilerOptions. (path (:sysroot parsed)) (path (:producer-bundle parsed)) (path (:cache parsed)))
        builder (-> (ProjectOptions/builder compiler)
                    (.rootModule (get parsed :root-module "Main")) (.sourceRoot (get parsed :source-root ".")))]
    (doseq [[name profile] (:entries parsed)]
      (case profile
        :auto (.function builder name)
        :nat-to-nat (.natFunction builder name)
        :string-to-string (.stringFunction builder name)
        :io-unit (.main builder name)))
    (.build builder)))
(defn- prepare-file! [parsed]
  (let [destination (.normalize (.toAbsolutePath (path (:output parsed))))
        parent (.getParent destination)
        options (cli-options parsed)]
    (need (Files/notExists destination (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
          "ArtifactExists" "Artifact output already exists or cannot be inspected")
    (Files/createDirectories parent (make-array FileAttribute 0))
    (let [temporary (Files/createTempFile parent ".lean-preparation-" ".zip" (make-array FileAttribute 0))]
      (with-cleanup
        (fn []
          (let [output (Files/newOutputStream temporary (into-array OpenOption [StandardOpenOption/WRITE]))
                descriptor (with-cleanup #(LeanPreparation/prepareProject (path (:source parsed)) options output)
                                        #(.close output))]
            ;; ATOMIC_MOVE can replace an existing destination despite omitted
            ;; REPLACE_EXISTING. A same-directory hard link atomically fails if
            ;; the destination exists; source compilation already requires Linux.
            (Files/createLink destination temporary)
            {:manifest-sha256 (.manifestSHA256 descriptor) :archive-sha256 (.archiveSHA256 descriptor)}))
        #(Files/deleteIfExists temporary)))))
(defn cli-status
  "Reusable CLI driver: print bounded JSON and return a status, never exit/close
   stdout/stderr. Only -main / Java main own process termination."
  [arguments]
  (try
    (let [parsed (parse-cli arguments)]
      (if (:help parsed) (print usage) (println (json/write-str (prepare-file! parsed))))
      (flush) 0)
    (catch Exception error
      (let [code (cond (instance? LeanException error) (.code ^LeanException error)
                       (instance? java.nio.file.FileAlreadyExistsException error) "ArtifactExists"
                       :else (or (:code (ex-data error)) "PreparationFailed"))
            message (or (.getMessage error) "Preparation failed")
            bounded #(subs (str %) 0 (min %2 (count (str %))))]
        (binding [*out* *err*]
          (println (json/write-str {:code (bounded code 96) :message (bounded message 2048)})) (flush))
        2))))
(defn -main [& arguments]
  (let [status (try (cli-status arguments) (finally (shutdown-agents)))]
    (when-not (zero? status) (System/exit status))))
