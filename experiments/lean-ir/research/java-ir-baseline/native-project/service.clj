(ns native-project-service-v1
  "Prototype JVM-owned project-path build/cache invocation. Python is an internal
   research helper here, not the promised public Java packaging dependency."
  (:require [clojure.java.io :as io] [native-project-entry-v1 :as entry])
  (:import [java.lang Process ProcessBuilder ProcessHandle]
           [java.nio.file Path Files LinkOption]
           [java.util WeakHashMap ArrayList] [java.util.concurrent TimeUnit]))
(deftype Loader [])
(defonce ^:private loaders (WeakHashMap.))
(defn- need [ok text] (when-not ok (throw (ex-info text {:profile :native-project-service-v1}))))
(defn- path! [value]
  (need (or (string? value) (instance? Path value)) "Filesystem path required")
  (.toRealPath (.toAbsolutePath (.toPath (io/file (str value)))) (make-array LinkOption 0)))
(defn- file-pin! [path pin]
  (need (and (string? pin) (re-matches #"[0-9a-f]{64}" pin)
             (= pin (#'entry/sha (#'entry/bytes! path 16777216)))) "Native build service code pin changed"))
(defn configure!
  "Configure trusted installed toolchain/helper once. The official installation
   is an explicit immutable dependency, not authenticated by githash alone.
   All expected pins come from host installation policy, never project files."
  [basis {:keys [python service service-sha256 sysroot exporter cache native-reference?]
          :or {native-reference? false}}]
  (need (or (string? cache) (instance? Path cache)) "Explicit project cache directory required")
  (need (boolean? native-reference?) "Explicit native comparison option required")
  (let [service (path! service) python (path! python) sysroot (path! sysroot) exporter (path! exporter)
        _ (file-pin! service service-sha256)
        cache-path (.toAbsolutePath (.toPath (io/file (str cache))))
        _ (Files/createDirectories cache-path (make-array java.nio.file.attribute.FileAttribute 0))
        cache (path! cache-path)
        token (Loader.)]
    (need (Files/isDirectory sysroot (make-array LinkOption 0)) "Installed official Lean sysroot required")
    ;; The exporter is larger than small JSON/helper bounds. The actual Python
    ;; service streams and checks its pinned binary before compiling or caching.
    (need (Files/isRegularFile exporter (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])) "Installed pinned exporter required")
    (locking loaders (.put loaders token {:basis basis :python python :service service :service-sha256 service-sha256
                                         :sysroot sysroot :exporter exporter :cache cache
                                         :native-reference? native-reference?})) token))
(defn- state [loader]
  (locking loaders (or (.get loaders loader) (throw (ex-info "Actual configured native project Loader required" {})))))
(defn- stop-process! [^Process process]
  ;; No guest engine exists during compilation. Terminate the owned compiler
  ;; process tree only; never close or unwind a Java runtime on this path.
  (with-open [descendants (.descendants (.toHandle process))]
    (.forEach descendants (reify java.util.function.Consumer
                            (accept [_ child] (.destroyForcibly ^ProcessHandle child)))))
  (.destroyForcibly process))
(defn- abort-build! [journal cause]
  (let [process (aget ^objects (:process-slot journal) 0)
        interrupted (or (instance? InterruptedException cause) (.isInterrupted (Thread/currentThread)))
        stop-failure (try (when (and process (.isAlive ^Process process)) (stop-process! process)) nil
                          (catch Throwable stop-error (.getName (class stop-error)))
                          (finally (when interrupted (.interrupt (Thread/currentThread)))))]
    ;; Keep the actual handle even if termination throws/remains asynchronous.
    ;; A failed build is not silently relabelled a completed native operation.
    (ex-info "Project compilation/preparation failed before Java execution"
             (cond-> journal stop-failure (assoc :stop-failure-class stop-failure)) cause)))
(defn load-project!
  "Load captured project path through actual pinned compile/cache service, then
   authenticate and prepare its immutable JavaIR Artifact. No Java engine opens
   before the native boundary returns ready. There is no fallback after IO."
  [loader project-directory]
  (let [{:keys [basis python service service-sha256 sysroot exporter cache native-reference?]} (state loader)
        project (path! project-directory)
        _ (need (Files/isDirectory project (make-array LinkOption 0)) "Project directory required")
        _ (file-pin! service service-sha256)
        output (Files/createTempFile cache ".native-client-" ".stdout" (make-array java.nio.file.attribute.FileAttribute 0))
        errors (Files/createTempFile cache ".native-client-" ".stderr" (make-array java.nio.file.attribute.FileAttribute 0))
        arguments (cond-> [(str python) "-I" (str service) "--project" (str project) "--cache" (str cache)
                           "--sysroot" (str sysroot) "--exporter" (str exporter)]
                    native-reference? (conj "--native-reference"))
        builder (doto (ProcessBuilder. ^java.util.List (ArrayList. arguments))
                  (.directory (.toFile cache)) (.redirectOutput (.toFile output)) (.redirectError (.toFile errors)))
        process-slot (object-array 1)
        journal {:stdout-file (str output) :stderr-file (str errors) :project (str project) :process-slot process-slot}]
    (try
      (let [^Process process (.start ^ProcessBuilder builder)]
        (aset ^objects process-slot 0 process)
        (when-not (.waitFor process 180 TimeUnit/SECONDS)
          (stop-process! process)
          (throw (ex-info "Native project build deadline exceeded; no Java engine started" journal)))
        (let [status (#'entry/json! (#'entry/text! (#'entry/bytes! output 16384)))]
          (need (and (zero? (.exitValue process)) (= "ready" (get status "status"))) "Native project service did not return ready")
          (file-pin! service service-sha256)
          (let [manifest (path! (get status "manifest")) artifact-root (.getParent manifest)]
            (need (and (.startsWith manifest cache) (= "manifest.json" (str (.getFileName manifest))))
                  "Build service returned an artifact outside its configured cache")
            {:artifact (entry/prepare! basis (str artifact-root) (get status "manifestSHA256"))
             :mode :official-native-frontend-java-ir-entry :cache-hit (get status "cacheHit")
             :cache-key (get status "cacheKey") :build-journal journal})))
      (catch Throwable cause
        (throw (abort-build! journal cause))))))
