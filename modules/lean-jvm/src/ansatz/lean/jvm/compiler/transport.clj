(ns ansatz.lean.jvm.compiler.transport
  "Shared bounded native producer transport. Loaded only by explicit source
   compilation; precompiled artifact loading does not initialize this service."
  (:require [ansatz.lean.jvm.producer :as producer] [clojure.java.io :as io] [clojure.data.json :as json]
            [clojure.string :as str] [ansatz.lean.jvm.compiler.encoding :as encoding])
  (:import [java.nio.file Path Files LinkOption StandardOpenOption StandardCopyOption FileAlreadyExistsException DirectoryNotEmptyException]
           [java.nio.file.attribute FileTime FileAttribute]
           [java.nio.channels FileChannel]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest] [java.util WeakHashMap ArrayList]
           [java.lang Process ProcessBuilder ProcessHandle]
           [java.util.concurrent TimeUnit]))

(def profile "ansatz-native-local-transport/1")
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def typed-source-pin "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041")
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
(defn- read-json! [path maximum] (encoding/json! (encoding/text! (bytes! path maximum))))
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
  "Explicit trusted Linux toolchain and independently pinned typed source helper.
   The producer bundle service checks all helper/source pins before this call."
  [{:keys [sysroot typed-source cache resource-launcher]}]
  (guard-code!)
  (need cache "An explicit compiler cache is required")
  (let [sysroot (path! sysroot) producer (executable! typed-source)
        producer-record (file-record producer (* 256 1024 1024))
        launcher (find-launcher! resource-launcher)
        _ (need (and (Files/isDirectory (.resolve sysroot "lib/lean") no-links)
                     (producer/binary-supported? "typedSource" (get producer-record "sha256")))
                "Pinned typed source producer/sysroot differs")
        _ (executable! (.resolve sysroot "bin/lean"))
        cache-path (.normalize (.toAbsolutePath (.toPath (io/file (str cache)))))
        _ (need (and (not (str/includes? (str cache-path) ":"))
                     (not (str/includes? (str sysroot) ":"))) "Explicit Linux cache/sysroot search paths required")
        _ (Files/createDirectories cache-path no-attributes)
        token (NativeCompiler.)]
    (locking compilers
      (.put compilers token {:sysroot sysroot :producer producer :producer-sha256 (get producer-record "sha256")
                            :launcher launcher :cache (path! cache-path)
                            :native-reference? false :lock (Object.) :journal nil})) token))
(defn cache-root [compiler] (guard-code!) (:cache (issued compiler)))
(defn close! [compiler]
  (let [state (issued compiler)]
    (locking (:lock state)
      (need (identical? state (issued compiler)) "Compiler identity changed while closing")
      (locking compilers (.remove compilers compiler)))) nil)

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
    (catch java.io.IOException error
      ;; proc(5) can disappear during a buffered read as generic IOException
      ;; (ESRCH), not only NoSuchFileException. Reobserve the actual handle;
      ;; missing live measurements use the existing bounded evidence resampler.
      (when (or (instance? java.io.InterruptedIOException error)
                (.isInterrupted (Thread/currentThread)))
        (.interrupt (Thread/currentThread))
        (throw error))
      (if (.isAlive process)
        (throw (ex-info "Live process status read unavailable"
                        {:profile profile :pid (.pid process) :process-alive? true
                         :status-unavailable true :rss-unavailable true
                         :read-failure-class (.getName (class error))} error))
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
          (when-not (and (zero? (.exitValue process))
                         (or (zero? (Files/size stderr))
                             ;; Only the independently pinned diagnostics-aware producer
                             ;; may write bounded stderr while returning structural data.
                             (and (= (str (:producer state)) (str (first arguments)))
                                  (producer/diagnostics-supported? (:producer-sha256 state)))))
            (let [text (String. ^bytes (bytes! stderr (* 1024 1024)) StandardCharsets/UTF_8)
                  detail (subs text 0 (min 1536 (count text)))]
              (throw (ex-info (str "Lean producer failed during " label
                                  (when (seq detail) (str ": " detail)))
                              {:code "NativeCompilationFailed" :stage label :exit (.exitValue process)}))))
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
        reported (str/trim (encoding/text! (bytes! (.resolve directory (get commit "stdout")) 16384)))
        version-text (str/trim (encoding/text! (bytes! (.resolve directory (get version "stdout")) 16384)))
        _ (need (and (= lean-pin reported) (str/includes? version-text "4.33.1")) "Installed Lean reports another supported version")
        inventory (library-inventory library)
        producer (file-record (:producer state) (* 256 1024 1024))
        _ (need (= (:producer-sha256 state) (get producer "sha256")) "Pinned typed source producer changed")]
    {"policy" "trusted-immutable-installed-official-toolchain/1" "sysroot" (str root)
     "reportedCommit" reported "reportedVersion" version-text "leanExecutable" (file-record lean (* 32 1024 1024))
     "typedSourceProducer" producer "typedSourceProducerPath" (str (:producer state))
     "resourceLauncher" (file-record (:launcher state) (* 16 1024 1024)) "resourceLauncherPath" (str (:launcher state))
     "initLibraryStatInventorySHA256" (digest (canonical inventory)) "initLibraryFiles" (count inventory)
     "fullLibraryByteAuthentication" false}))

(defn- read-stream! [^Path path]
  (let [text (encoding/text! (bytes! path max-bytes)) lines (str/split-lines text)
        _ (need (<= 1 (count lines) 20001) "IR stream row bound")
        manifest (encoding/json! (first lines)) rows (mapv encoding/json! (rest lines))]
    (need (and (= "lean-ir-probe/1" (get manifest "schema")) (= "4.33.1" (get manifest "leanVersion"))
               (= {"target" "x86_64-unknown-linux-gnu" "wordBits" 64} (get manifest "runtimeProfile"))
               (every? #(= "decl" (get % "kind")) rows)) "Missing/unsupported native IR stream")
    [manifest rows]))
