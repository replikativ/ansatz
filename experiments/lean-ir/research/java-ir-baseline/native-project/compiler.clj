(ns native-project-compiler-v1
  "Internal JVM-owned compiler/cache for the pinned first-Lake profile. Native
   checker/compiler trust, not hosted Init or Java kernel authority. No Python."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]
            [clojure.string :as str] [native-project-entry-v1 :as entry])
  (:import [java.nio.file Path Files LinkOption StandardOpenOption StandardCopyOption FileAlreadyExistsException DirectoryNotEmptyException]
           [java.nio.file.attribute FileTime FileAttribute]
           [java.nio.channels FileChannel]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest] [java.util WeakHashMap ArrayList]
           [java.lang Process ProcessBuilder ProcessHandle]
           [java.util.concurrent TimeUnit]))

(def profile "fp-lean-first-lake-native-4331-jvm/1")
(def lean-pin entry/lean-pin)
(def exporter-pin entry/exporter-pin)
(def source-pins
  {"Greeting/Basic.lean" "b186dbcbc8cd3f04b6f9d39f4f130996ee75093b3d0923a9ceda2e2b70220afb"
   "Greeting.lean" "b23733091936f7b4318c98880382dc901d5ca5830870bd40bbaa1128cbc91ed2"
   "Main.lean" "84b2361691c0d105c438b137563c447e36e38827aaa633707ca99d14c4d20316"
   "lakefile.toml" "d66a3f6386de06f0f3666cde3101ec1c71884c9f2678a41c69aac1f5d5834c80"})
(def modules [["Greeting.Basic" "Greeting/Basic.lean"] ["Greeting" "Greeting.lean"] ["Main" "Main.lean"]])
(def max-bytes (* 32 1024 1024))
(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(def ^:private no-attributes (make-array FileAttribute 0))
(deftype NativeCompiler [])
(defonce ^:private compilers (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile profile}))))
(defn- path! [value]
  (need (or (string? value) (instance? Path value)) "Explicit filesystem path required")
  (.toRealPath (.toAbsolutePath (.toPath (io/file (str value)))) (make-array LinkOption 0)))
(defn- regular! [^Path path]
  (need (and (not (Files/isSymbolicLink path)) (Files/isRegularFile path no-links)) "Regular non-symlink file required") path)
(defn- stamp [^Path path]
  (regular! path)
  (let [a (Files/readAttributes path "unix:dev,ino,size,lastModifiedTime,ctime" no-links)]
    [(.get a "dev") (.get a "ino") (.get a "size")
     (.to ^FileTime (.get a "lastModifiedTime") TimeUnit/NANOSECONDS)
     (.to ^FileTime (.get a "ctime") TimeUnit/NANOSECONDS)]))
(defn- hex [bytes] (apply str (map #(format "%02x" (bit-and 255 %)) bytes)))
(defn- digest [^bytes bytes] (hex (.digest (MessageDigest/getInstance "SHA-256") bytes)))
(defn- file-record [^Path path maximum]
  (let [before (stamp path) _ (need (<= 0 (nth before 2) maximum) "File extent exceeds bound")
        hash (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
    (with-open [input (Files/newInputStream path (make-array java.nio.file.OpenOption 0))]
      (loop [total 0]
        (let [n (.read input buffer)]
          (when (pos? n)
            (need (<= (+ total n) maximum) "File grew past bound")
            (.update hash buffer 0 n) (recur (+ total n))))))
    (need (= before (stamp path)) "File changed during hash")
    {"bytes" (nth before 2) "sha256" (hex (.digest hash))}))
(defn- bytes! [^Path path maximum]
  (let [before (stamp path) _ (need (<= 0 (nth before 2) maximum) "Metadata extent exceeds bound")
        data (with-open [input (Files/newInputStream path (make-array java.nio.file.OpenOption 0))]
               (.readNBytes input (int (inc maximum))))]
    (need (and (<= (alength data) maximum) (= before (stamp path))) "Metadata changed during read") data))
(defn- ordered [value]
  (cond (map? value) (into (sorted-map) (map (fn [[k v]] [(str k) (ordered v)]) value))
        (sequential? value) (mapv ordered value) :else value))
(defn- canonical [value] (.getBytes (json/write-str (ordered value)) StandardCharsets/UTF_8))
(defn- read-json! [path maximum] (#'entry/json! (#'entry/text! (bytes! path maximum))))
(defn- write-json! [^Path path value]
  (let [data (canonical value)]
    (with-open [channel (FileChannel/open path (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))]
      (let [buffer (java.nio.ByteBuffer/wrap data)] (while (.hasRemaining buffer) (.write channel buffer)))
      (.force channel true))) path)
(defn- implementation-source! [source-name]
  (let [file (io/file source-name)]
    (if (.isFile file)
      {:file (path! source-name)}
      (let [url (io/resource source-name)]
        (need (and url
                   (case (.getProtocol ^java.net.URL url)
                     "file" true
                     "jar" (= "file" (.getProtocol (.getJarFileURL ^java.net.JarURLConnection (.openConnection url))))
                     false))
              "Compiler source must be present as a file or bundled classpath resource")
        {:url url}))))
(defn- source-record! [{:keys [file url]}]
  (if file (file-record file (* 2 1024 1024))
    (let [connection (.openConnection ^java.net.URL url)
          _ (.setUseCaches connection false)
          bytes (with-open [input (.getInputStream connection)]
                  (.readNBytes input (inc (* 2 1024 1024))))]
      (need (<= (alength bytes) (* 2 1024 1024)) "Bundled compiler source extent exceeds bound")
      {"bytes" (alength bytes) "sha256" (digest bytes)})))
(def ^:private implementation-source (implementation-source! *file*))
(def ^:private implementation-record (source-record! implementation-source))
(defn- guard-code! []
  (need (= implementation-record (source-record! implementation-source)) "Loaded compiler source changed; configure a new reviewed version"))
(defn- issued [compiler]
  (locking compilers (or (.get compilers compiler) (throw (ex-info "Actual configured internal Compiler required" {})))))
(defn- proc-text! [path]
  ;; Pseudo-files may report length zero and reject available(2). A buffered
  ;; character read uses actual bounded bytes rather than FileInputStream's
  ;; whole-file optimizations (notably on newer JDKs).
  (with-open [reader (Files/newBufferedReader (.toPath (io/file path)) StandardCharsets/UTF_8)]
    (let [buffer (char-array 4096) result (StringBuilder.)]
      (loop [total 0]
        (let [n (.read reader buffer 0 (alength buffer))]
          (if (neg? n) (.toString result)
            (do (need (<= (+ total n) 65536) "Linux process evidence exceeds bound")
                (.append result buffer 0 n) (recur (+ total n)))))))))
(defn- available-kib []
  (let [text (proc-text! "/proc/meminfo") m (re-find #"(?m)^MemAvailable:\s+(\d+)\s+kB$" text)]
    (need m "Linux MemAvailable evidence unavailable") (Long/parseLong (second m))))
(defn- executable! [value]
  (let [p (path! value)] (regular! p) (need (Files/isExecutable p) "Executable file required") p))
(defn- find-launcher! [supplied]
  (if supplied (executable! supplied)
    (or (some (fn [root]
                (when (and (seq root) (.isAbsolute (.toPath (io/file root))))
                  (let [p (.resolve (.toPath (io/file root)) "prlimit")]
                    (when (and (Files/isRegularFile p no-links) (Files/isExecutable p)) (executable! p)))))
              (str/split (or (System/getenv "PATH") "") #":"))
        (throw (ex-info "Linux prlimit launcher required for the reviewed hard resource limits" {})))))
(defn configure!
  "Configure an internal backend before effects. The installed official sysroot
   and cache are trusted dependencies, not fully byte-attested library stores."
  [{:keys [sysroot exporter cache resource-launcher native-reference?] :or {native-reference? false}}]
  (guard-code!)
  (need (and cache (boolean? native-reference?)) "Explicit cache and native reference option required")
  (let [sysroot (path! sysroot) exporter (executable! exporter) launcher (find-launcher! resource-launcher)
        _ (need (and (Files/isDirectory (.resolve sysroot "lib/lean") no-links)
                     (= exporter-pin (get (file-record exporter (* 256 1024 1024)) "sha256"))) "Pinned exporter/sysroot differs")
        _ (executable! (.resolve sysroot "bin/lean"))
        cache-path (.normalize (.toAbsolutePath (.toPath (io/file (str cache)))))
        _ (need (and cache (not (str/includes? (str cache-path) ":"))
                     (not (str/includes? (str sysroot) ":"))) "Explicit Linux cache/sysroot search paths required")
        _ (Files/createDirectories cache-path no-attributes)
        token (NativeCompiler.)]
    (locking compilers
      (.put compilers token {:sysroot sysroot :exporter exporter :launcher launcher :cache (path! cache-path)
                            :native-reference? native-reference? :lock (Object.) :journal nil})) token))
(defn cache-root [compiler] (guard-code!) (:cache (issued compiler)))
(defn close! [compiler]
  (let [state (issued compiler)]
    (locking (:lock state)
      (need (identical? state (issued compiler)) "Compiler identity changed while closing")
      (locking compilers (.remove compilers compiler)))) nil)

(defn- source-capture [^Path project]
  (into (sorted-map)
    (for [[relative expected] source-pins
          :let [path (.resolve project relative)
                _ (loop [p path]
                    (when-not (= p project)
                      (need (and p (.startsWith p project) (not (Files/isSymbolicLink p))) "Source symlink/path escape")
                      (recur (.getParent p))))
                bytes (bytes! path 65536) record {"bytes" (alength bytes) "sha256" (digest bytes)}]]
      (do (need (= expected (get record "sha256")) "Unsupported or modified selected project source")
          [relative {:bytes bytes :record record}]))))
(defn- records [capture] (into (sorted-map) (map (fn [[p value]] [p (:record value)]) capture)))
(defn- environment [state search]
  {"LEAN_NUM_THREADS" "1" "MALLOC_ARENA_MAX" "1" "LEAN_SYSROOT" (str (:sysroot state))
   "LEAN_PATH" search "PATH" (str (.resolve ^Path (:sysroot state) "bin") ":" (or (System/getenv "PATH") ""))})
(defn- stop-process! [^Process process]
  (with-open [children (.descendants (.toHandle process))]
    (.forEach children (reify java.util.function.Consumer (accept [_ child] (.destroyForcibly ^ProcessHandle child)))))
  ;; Like the existing client, do not introduce an interruptible wait while
  ;; already handling cancellation. The actual handle remains in the journal.
  (.destroyForcibly process)
  process)
(defn- abort! [journal cause]
  (let [process (aget ^objects (:process-slot @journal) 0)
        interrupted (or (instance? InterruptedException cause) (.isInterrupted (Thread/currentThread)))
        stop-error (try
                     ;; Keep observed descendants even if their parent exited.
                     (when-let [handles (:process-handles @journal)]
                       (doseq [^ProcessHandle handle @handles]
                         (when (.isAlive handle) (.destroyForcibly handle))))
                     (when (and process (.isAlive ^Process process)) (stop-process! process)) nil
                        (catch Throwable error (.getName (class error)))
                        (finally (when interrupted (.interrupt (Thread/currentThread)))))]
    (swap! journal assoc :status :failed :stop-failure-class stop-error)
    (throw (ex-info "Native compilation failed before any Java guest engine; preserve compiler journal" {:journal @journal} cause))))
(defn- rss-from-status! [pid text alive?]
  (let [rss (re-find #"(?m)^VmRSS:\s+(\d+)\s+kB$" text)
        state (second (re-find #"(?m)^State:\s+([A-Za-z])(?:\s|$)" text))]
    (cond rss (Long/parseLong (second rss))
          ;; Linux removes the mm before the zombie/dead task is reaped;
          ;; ProcessHandle.isAlive can still be true in that interval.
          (or (#{"Z" "X" "x"} state) (not alive?)) 0
          :else (throw (ex-info "Live process RSS unavailable"
                                {:profile profile :pid pid :kernel-state state
                                 :process-alive? alive? :status text :rss-unavailable true})))))
(defn- sample-handle-rss-kib [^ProcessHandle process]
  (try
    (let [text (proc-text! (str "/proc/" (.pid process) "/status"))]
      (rss-from-status! (.pid process) text (.isAlive process)))
    (catch java.nio.file.NoSuchFileException error
      (if (.isAlive process)
        (throw (ex-info "Live process status vanished"
                        {:profile profile :pid (.pid process) :process-alive? true :status-unavailable true} error))
        0))))
(defn- pause-rss-sample! []
  (try (Thread/sleep 1)
       (catch InterruptedException error
         (.interrupt (Thread/currentThread))
         (throw error))))
(defn- handle-rss-kib [^ProcessHandle process]
  ;; proc_pid_status samples task state before obtaining mm. An exiting task
  ;; can therefore have a live-looking state and no VmRSS in one snapshot.
  ;; Resample evidence only; never retry the native command or infer zero.
  (loop [sample 1 initial nil]
    (let [result (try {:rss (sample-handle-rss-kib process)}
                     (catch clojure.lang.ExceptionInfo error
                       (if (:rss-unavailable (ex-data error)) {:missing error} (throw error))))]
      (if (contains? result :rss) (:rss result)
        (let [error (:missing result) latest (ex-data error) first-status (or initial (:status latest))]
          (if (< sample 3)
            (do (pause-rss-sample!) (recur (inc sample) first-status))
            (throw (ex-info "Live process RSS unavailable after bounded status resampling"
                            (assoc latest :first-status first-status :latest-status (:status latest)
                                   :status-samples sample)
                            error))))))))
(defn- remember-process! [handles handle]
  ;; Publish each handle before a bound can fail, so cancellation retains it.
  (swap! handles #(if (some #{handle} %) % (conj % handle)))
  (need (<= (count @handles) 64) "Owned native process count exceeds bound"))
(defn- owned-rss-kib [handles]
  (reduce + 0 (map #(if (.isAlive ^ProcessHandle %) (handle-rss-kib %) 0) @handles)))
(defn- rss-kib [^Process process handles]
  (remember-process! handles (.toHandle process))
  (with-open [children (.descendants (.toHandle process))]
    (doseq [handle (iterator-seq (.iterator children))] (remember-process! handles handle)))
  (owned-rss-kib handles))
(defn- check-build-deadline! [state]
  (when-let [start (:build-start-nanos state)]
    (need (< (- (System/nanoTime) start) (:max-build-nanos state)) "Native aggregate build deadline exceeded")))
(defn- run-process! [state journal ^Path directory label arguments env]
  (check-build-deadline! state)
  (need (>= (available-kib) (* 2 1024 1024)) "MemAvailable below 2 GiB floor; no native process started")
  (let [stdout (.resolve directory (str label ".jsonl")) stderr (.resolve directory (str label ".stderr"))
        argv (into [(str (:launcher state)) "--cpu=90:90" "--core=0:0" "--fsize=33554432:33554432" "--"] (mapv str arguments))
        builder (doto (ProcessBuilder. ^java.util.List (ArrayList. argv))
                  (.directory (.toFile ^Path (or (:working-directory state) directory)))
                  (.redirectOutput (.toFile stdout)) (.redirectError (.toFile stderr)))
        _ (.putAll (.environment builder) env)
        slot (object-array 1) handles (atom []) start (System/nanoTime) peak (atom 0)]
    (swap! journal assoc :stage label :process-slot slot :process-handles handles :stdout-file (str stdout) :stderr-file (str stderr))
    (try
      (let [^Process process (.start builder)]
        (aset slot 0 process)
        (remember-process! handles (.toHandle process))
        (loop []
          (when-not (.waitFor process 20 TimeUnit/MILLISECONDS)
            (check-build-deadline! state)
            (swap! peak max (rss-kib process handles))
            (need (<= @peak (* 900 1024)) "Native RSS exceeds 900 MiB")
            (need (>= (available-kib) (* 2 1024 1024)) "Native MemAvailable below 2 GiB")
            (need (<= (- (System/nanoTime) start) 120000000000) "Native wall deadline exceeded")
            (need (and (<= (Files/size stdout) max-bytes) (<= (Files/size stderr) (* 1024 1024))) "Native output extent exceeded")
            (recur)))
        (check-build-deadline! state)
        (need (not-any? #(.isAlive ^ProcessHandle %) @handles) "Owned native descendant still running after compiler exit")
        (let [receipt {"label" label "command" argv "exit" (.exitValue process)
                       "stdout" (str (.getFileName stdout)) "stdoutRecord" (file-record stdout max-bytes)
                       "stderr" (str (.getFileName stderr)) "stderrRecord" (file-record stderr (* 1024 1024))
                       "elapsedSeconds" (/ (- (System/nanoTime) start) 1.0e9) "peakSampledRSSKiB" @peak
                       "RSSScope" "root-and-observed-owned-descendants"}]
          (write-json! (.resolve directory (str label ".receipt.json")) receipt)
          (swap! journal update :processes (fnil conj []) receipt)
          (need (and (zero? (.exitValue process)) (zero? (Files/size stderr))) "Native compiler returned failure/diagnostics")
          receipt))
      (catch Throwable error (abort! journal error)))))

(defn- library-inventory [^Path library]
  (let [init (.resolve library "Init")
        roots (with-open [s (Files/list library)]
                (vec (filter #(str/starts-with? (str (.getFileName ^Path %)) "Init.") (iterator-seq (.iterator s)))))
        paths (with-open [s (Files/walk init (make-array java.nio.file.FileVisitOption 0))]
                (reduce (fn [out path]
                          (need (and (< (count out) 4096) (not (Files/isSymbolicLink path))) "Init library inventory bound/symlink")
                          (if (Files/isRegularFile path no-links) (conj out path) out)) roots (iterator-seq (.iterator s))))]
    (need (<= 1 (count paths) 4096) "Installed Init inventory absent or excessive")
    (mapv (fn [^Path p] [(str (.relativize library p)) (stamp p)]) (sort-by str paths))))
(defn- toolchain! [state journal ^Path directory]
  (let [root ^Path (:sysroot state) lean (.resolve root "bin/lean") library (.resolve root "lib/lean")
        env (environment state (str library))
        suffix (str (java.util.UUID/randomUUID))
        commit (run-process! state journal directory (str "identity-commit-" suffix) [lean "--githash"] env)
        version (run-process! state journal directory (str "identity-version-" suffix) [lean "--version"] env)
        reported (str/trim (#'entry/text! (bytes! (.resolve directory (get commit "stdout")) 16384)))
        version-text (str/trim (#'entry/text! (bytes! (.resolve directory (get version "stdout")) 16384)))
        _ (need (and (= lean-pin reported) (str/includes? version-text "4.33.1")) "Installed Lean reports another supported version")
        inventory (library-inventory library)
        exporter (file-record (:exporter state) (* 256 1024 1024))
        _ (need (= exporter-pin (get exporter "sha256")) "Pinned exporter changed")]
    {"policy" "trusted-immutable-installed-official-toolchain/1" "sysroot" (str root)
     "reportedCommit" reported "reportedVersion" version-text "leanExecutable" (file-record lean (* 32 1024 1024))
     "exporter" exporter "exporterPath" (str (:exporter state))
     "resourceLauncher" (file-record (:launcher state) (* 16 1024 1024)) "resourceLauncherPath" (str (:launcher state))
     "initLibraryStatInventorySHA256" (digest (canonical inventory)) "initLibraryFiles" (count inventory)
     "fullLibraryByteAuthentication" false}))

(defn- inventory [^Path root]
  (loop [pending [root] visited 0 result (sorted-map)]
    (need (and (<= visited 256) (<= (count pending) 256) (<= (count result) 128)) "Artifact directory traversal bound")
    (if (empty? pending) result
      (let [path ^Path (peek pending) tail (pop pending)]
        (need (not (Files/isSymbolicLink path)) "Symlink in artifact directory")
        (if (Files/isDirectory path no-links)
          (let [children (with-open [s (Files/list path)]
                           (reduce (fn [xs p] (need (< (count xs) 256) "Artifact directory fanout bound") (conj xs p))
                                   [] (iterator-seq (.iterator s))))]
            (recur (into tail children) (inc visited) result))
          (let [relative (str (.relativize root path))]
            (regular! path)
            (recur tail (inc visited)
                   (if (= relative "manifest.json") result (assoc result relative (file-record path max-bytes))))))))))
(defn- validate-hit! [^Path directory key inputs]
  (need (and (Files/isDirectory directory no-links) (not (Files/isSymbolicLink directory))) "Invalid cache entry directory")
  (let [raw (bytes! (.resolve directory "manifest.json") (* 4 1024 1024))
        manifest (#'entry/json! (#'entry/text! raw))]
    (need (and (= "native-compiled-project/1" (get manifest "schema")) (= key (get manifest "cacheKey"))
               (= inputs (get manifest "inputs")) (= (get manifest "files") (inventory directory)))
          "Cache key/profile or complete file set changed")
    {:manifest manifest :sha256 (digest raw)}))
(defn- typed-name [label] (reduce (fn [prefix part] ["str" prefix part]) ["anonymous"] (str/split label #"\.")))
(defn- read-stream! [^Path path]
  (let [text (#'entry/text! (bytes! path max-bytes)) lines (str/split-lines text)
        _ (need (<= 1 (count lines) 20001) "IR stream row bound")
        manifest (#'entry/json! (first lines)) rows (mapv #'entry/json! (rest lines))]
    (need (and (= "lean-ir-probe/1" (get manifest "schema")) (= "4.33.1" (get manifest "leanVersion"))
               (= {"target" "x86_64-unknown-linux-gnu" "wordBits" 64} (get manifest "runtimeProfile"))
               (every? #(= "decl" (get % "kind")) rows)) "Missing/unsupported native IR stream")
    [manifest rows]))
(defn- copy-capture! [^Path directory capture]
  (doseq [[relative value] capture]
    (let [path (.resolve directory relative)]
      (Files/createDirectories (.getParent path) no-attributes)
      (Files/write path ^bytes (:bytes value)
                   (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
      (need (= (:record value) (file-record path 65536)) "Private source capture bytes changed"))))
(defn- publish! [^Path stage ^Path target key inputs]
  ;; Both directories have the same cache parent. Existing accepted entries are
  ;; immutable. A concurrent winning publication must independently revalidate.
  (try
    (Files/move stage target (into-array java.nio.file.CopyOption [StandardCopyOption/ATOMIC_MOVE]))
    (catch FileAlreadyExistsException _ (validate-hit! target key inputs))
    (catch DirectoryNotEmptyException _ (validate-hit! target key inputs)))
  (validate-hit! target key inputs))
(defn- ready [^Path target key pin hit?]
  {"status" "ready" "cacheHit" hit? "cacheKey" key "manifest" (str (.resolve target "manifest.json")) "manifestSHA256" pin})
(defn compile!
  "Compile/cache the immutable selected source capture. JOURNAL is caller-owned
   and published before any native start. It retains failures and actual process
   handles; this operation owns no guest engine and never retries another backend."
  [compiler project-directory journal]
  (guard-code!)
  (need (and (instance? clojure.lang.IAtom journal) (= {} @journal)) "Fresh compiler journal atom required")
  (let [state (issued compiler)]
    (locking (:lock state)
      (need (identical? state (issued compiler)) "Compiler identity changed while waiting to compile")
      (let [project (path! project-directory)
            _ (need (Files/isDirectory project no-links) "Project directory required")
            capture (source-capture project) original-records (records capture)
            cache ^Path (:cache state)
            probe (Files/createTempDirectory cache ".jvm-identity-" no-attributes)]
        (swap! journal assoc :status :preflight :project (str project) :identity-directory (str probe)
               :process-slot (object-array 1) :processes [])
        (try
          (let [toolchain (toolchain! state journal probe)
                inputs {"profile" profile "compilerImplementation" implementation-record
                        "sources" original-records "toolchain" toolchain
                        "options" {"threads" 1 "nativeReference" (:native-reference? state)}}
                key (digest (canonical inputs)) target (.resolve cache key)]
            (swap! journal assoc :cache-key key :inputs inputs)
            (if (Files/exists target no-links)
              (let [validated (validate-hit! target key inputs)]
                (swap! journal assoc :status :ready :cache-hit true)
                (ready target key (:sha256 validated) true))
              (let [stage (Files/createTempDirectory cache (str ".jvm-build-" key "-") no-attributes)
                    copied (.resolve stage "project") build (.resolve stage "build")
                    _ (swap! journal assoc :stage-directory (str stage) :status :building)
                    _ (Files/createDirectories copied no-attributes) _ (Files/createDirectories build no-attributes)
                    _ (copy-capture! copied capture)
                    execution-state (assoc state :working-directory copied)
                    env (environment state (str build ":" (.resolve ^Path (:sysroot state) "lib/lean")))
                    ordered-modules
                    (mapv (fn [[label relative]]
                            (let [olean (.resolve build (str (str/replace label "." "/") ".olean"))
                                  _ (Files/createDirectories (.getParent olean) no-attributes)
                                  receipt (run-process! execution-state journal stage (str label "-local")
                                            [(:exporter state) "--source" (.resolve copied relative) "--olean" olean "--local" label] env)
                                  [manifest rows] (read-stream! (.resolve stage (get receipt "stdout")))
                                  plan (get manifest "initializationPlan")]
                              (need (and (= (typed-name label) (get plan "module")) (= [] (get plan "actions"))
                                         (every? #(and (true? (get % "sourceLocal")) (= (typed-name label) (get % "sourceModule"))) rows))
                                    "Selected local initialization/provenance differs")
                              {"module" label "typedModule" (typed-name label) "source" (str "project/" relative)
                               "sourceSHA256" (get-in original-records [relative "sha256"])
                               "olean" (str (.relativize stage olean)) "oleanSHA256" (get (file-record olean max-bytes) "sha256")
                               "localStream" (get receipt "stdout") "localStreamSHA256" (get-in receipt ["stdoutRecord" "sha256"])
                               "initPlan" plan "rowCount" (count rows)})) modules)
                    closure (run-process! execution-state journal stage "Main-closure"
                              [(:exporter state) "--source" (.resolve copied "Main.lean") "--closure" "Main" "main"] env)
                    [_ rows] (read-stream! (.resolve stage (get closure "stdout")))
                    names (set (map #(get % "name") rows))
                    _ (need (and (= (count names) (count rows))
                                 (every? names (mapcat #(get % "dependencies") rows))) "Incomplete actual static dependency closure")
                    main (some #(when (= (typed-name "main") (get % "name")) %) rows)
                    _ (need (and (= [{"borrow" false "ty" "void" "x" {"idx" 1}}] (get-in main ["ir" "fdecl" "xs"]))
                                 (= "object" (get-in main ["ir" "fdecl" "type"]))) "Original raw main IO ABI differs")
                    reference (when (:native-reference? state)
                                (let [r (run-process! execution-state journal stage "native-reference"
                                          [(.resolve ^Path (:sysroot state) "bin/lean") "--run" (.resolve copied "Main.lean")] env)
                                      bytes (bytes! (.resolve stage (get r "stdout")) 65536)]
                                  (need (java.util.Arrays/equals ^bytes bytes (.getBytes "Hello, world!\n" StandardCharsets/UTF_8))
                                        "Actual native reference output differs")
                                  {"receipt" "native-reference.receipt.json" "stdoutUTF8" (#'entry/text! bytes)
                                   "stdoutBytes" (alength bytes) "stdoutSHA256" (digest bytes) "exit" (get r "exit")}))
                    _ (need (and (= original-records (records (source-capture project)))
                                 (= original-records (records (source-capture copied)))) "Source changed during compilation")
                    _ (guard-code!)
                    after (toolchain! state journal stage)
                    _ (need (= toolchain after) "Trusted installed toolchain changed during compilation")
                    artifact {"schema" "native-compiled-project/1" "profile" profile "cacheKey" key "inputs" inputs
                              "producerLeanCommit" lean-pin "producerLeanVersion" "4.33.1" "target" "x86_64-unknown-linux-gnu"
                              "exporterSHA256" exporter-pin "compilerImplementation" implementation-record
                              "repositoryCommit" "0abeea545d560a324e2561f7210fbd6ed154fa02" "sourceFilesUnchanged" true
                              "orderedModules" ordered-modules "executionStream" (get closure "stdout")
                              "executionStreamSHA256" (get-in closure ["stdoutRecord" "sha256"])
                              "entry" (typed-name "main") "nativeReference" reference "staticDependencyClosureComplete" true
                              "dynamicClosureProven" false "guestModuleDataAccepted" false "guestKernelAccepted" false
                              "trustBoundary" "Official native frontend/checker/compiler; no hosted frontend or Java kernel rechecking"
                              "files" (inventory stage)}
                    _ (write-json! (.resolve stage "manifest.json") artifact)
                    _ (validate-hit! stage key inputs)
                    published (publish! stage target key inputs)]
                (swap! journal assoc :status :ready :cache-hit false :manifest-sha256 (:sha256 published))
                (ready target key (:sha256 published) false))))
          (catch Throwable cause (abort! journal cause)))))))
