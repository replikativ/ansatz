(ns native-local-project-v2
  "Internal source/compiled-module preparation. No artifact, entry or READY
   Project is issued here. Uses the fixed compiler's monitored native transport."
  (:require [native-project-compiler-v1 :as compiler]
            [clojure.string :as str]
            [clojure.data.json :as json])
  (:import [java.nio.file Path Files LinkOption StandardOpenOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio ByteBuffer CharBuffer]
           [java.util Locale]))

(def profile "native-local-project-prepare/2")
(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(def ^:private attrs (make-array FileAttribute 0))
(defn- require! [ok code facts]
  (when-not ok (throw (ex-info code (assoc facts :code code :profile profile)))))
(defn- utf8-size! [s]
  (require! (string? s) "ModulePathConflict" {})
  (try
    (.remaining (.encode (doto (.newEncoder StandardCharsets/UTF_8)
                           (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
                        (CharBuffer/wrap ^String s)))
    (catch java.nio.charset.CharacterCodingException _
      (require! false "ModulePathConflict" {:reason :invalid-unicode}))))
(defn- project-path! [value]
  (require! (or (string? value) (instance? Path value)) "UnsupportedProjectConfig" {})
  (let [absolute (.normalize (.toAbsolutePath (.toPath (clojure.java.io/file (str value)))))]
    (loop [p absolute]
      (when p
        (require! (not (Files/isSymbolicLink p)) "ModulePathConflict" {:path (str p)})
        (recur (.getParent p))))
    (require! (Files/isDirectory absolute no-links) "UnsupportedProjectConfig" {:project (str absolute)})
    (#'compiler/path! absolute)))
(defn module-components
  "Structural string Name only; a quoted dot remains one filesystem component."
  [name]
  (loop [n name parts [] depth 0 total 0]
    (require! (and (vector? n) (< depth 65) (<= total 4096)) "ModulePathConflict" {:name name})
    (cond
      (= n ["anonymous"]) (do (require! (seq parts) "ModulePathConflict" {:name name}) (vec (reverse parts)))
      (and (= 3 (count n)) (= "str" (first n)))
      (let [s (nth n 2)]
        (require! (and (string? s) (<= 1 (utf8-size! s) 255)
                       (not (#{"." ".." ".lake" ".git" "build"} s))
                       (not-any? #(or (= % \/) (= % \\) (= (int %) 0)) s))
                  "ModulePathConflict" {:name name})
        (recur (second n) (conj parts s) (inc depth) (+ total (utf8-size! s))))
      :else (require! false "ModulePathConflict" {:name name}))))
(defn module-relative [name] (str (str/join "/" (module-components name)) ".lean"))
(defn- init? [name] (= "Init" (first (module-components name))))
(defn- vector! [xs maximum code]
  (require! (and (vector? xs) (<= 1 (count xs) maximum)) code {}) xs)
(defn- source-path! [^Path root relative]
  (let [path (.normalize (.resolve root ^String relative))]
    (require! (.startsWith path root) "ModulePathConflict" {:relative relative})
    (loop [p path]
      (require! (and p (not (Files/isSymbolicLink p))) "ModulePathConflict" {:relative relative})
      (when-not (= p root) (recur (.getParent p))))
    path))
(defn- capture! [^Path root ^Path copied name]
  (let [relative (module-relative name) path (source-path! root relative)
        bytes (#'compiler/bytes! path 1048576)
        decoder (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
        _ (.decode decoder (ByteBuffer/wrap bytes))
        target (.resolve copied relative)]
    (Files/createDirectories (.getParent target) attrs)
    (Files/write target bytes (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
    {:name name :relative relative :record {"bytes" (alength bytes) "sha256" (#'compiler/digest bytes)}}))
(def ^:private init-name ["str" ["anonymous"] "Init"])
(defn- ordinary [name meta?] {"module" name "importAll" false "isExported" true "isMeta" meta?})
(defn- admit-header! [raw source captured-path]
  (let [h (get raw "header") explicit (get h "explicitImports") requested (get h "requestedImports")
        prefix [(ordinary init-name false) (ordinary init-name true)] bytes (get-in source [:record "bytes"])]
    (require! (and (= "lean-project-header/2" (get raw "schema"))
                   (= "NativeStartupEvidence.exportHeader" (get raw "producer"))
                   (= compiler/lean-pin (get raw "leanCommit")) (= "4.33.1" (get raw "leanVersion"))
                   (= (str captured-path) (get raw "fileName")) (= bytes (get raw "sourceUTF8Bytes"))
                   (= "disabled" (get raw "lineEndingNormalization")) (false? (get raw "parserHasErrors"))
                   (integer? (get raw "parserEndByte")) (<= 0 (get raw "parserEndByte") bytes)
                   (false? (get h "isModule")) (false? (get h "hasPrelude"))
                   (= "original-HeaderSyntax.imports-includeInit-false-and-true" (get h "interpretation"))
                   (vector? explicit) (<= (count explicit) 4094)
                   (= prefix (get h "insertedImportPrefix")) (= (into prefix explicit) requested)
                   (every? #(= % (ordinary (get % "module") false)) explicit))
              "HeaderRejected" {:module (:name source) :source (:record source)})
    (doseq [imp requested] (module-components (get imp "module"))) requested))

(defn dependency-order
  "Bounded typed DFS. Scheduling deduplicates; source import occurrences remain."
  [roots modules]
  (let [colors (atom {}) result (atom [])]
    (letfn [(visit [name path]
              (require! (<= (count path) 64) "BuildResourceLimit" {:path path})
              (case (get @colors name)
                :done nil
                :active (require! false "ImportCycle" {:cycle (conj (vec (drop-while #(not= name %) path)) name)})
                (do (require! (contains? modules name) "MissingDependency" {:module name})
                    (swap! colors assoc name :active)
                    (doseq [dep (:dependencies (get modules name))] (visit dep (conj path name)))
                    (swap! colors assoc name :done) (swap! result conj name))))]
      (doseq [root roots] (visit root [])) @result)))

(def ^:private implementation-source (#'compiler/implementation-source! *file*))
(def ^:private implementation-record (#'compiler/source-record! implementation-source))
(defn- inventory! [^Path root]
  (loop [pending [root] visited 0 total 0 files (sorted-map)]
    (require! (and (<= visited 4096) (<= (count pending) 4096) (<= total (* 64 1048576))) "BuildResourceLimit" {})
    (if (empty? pending) files
      (let [p ^Path (peek pending) tail (pop pending)]
        (require! (not (Files/isSymbolicLink p)) "ArtifactConflict" {:path (str p)})
        (if (Files/isDirectory p no-links)
          (let [children (with-open [stream (Files/list p)]
                           (reduce (fn [xs child]
                                     (require! (< (count xs) 4096) "BuildResourceLimit" {}) (conj xs child))
                                   [] (iterator-seq (.iterator stream))))]
            (recur (into tail children) (inc visited) total files))
          (let [relative (str (.relativize root p)) record (#'compiler/file-record p (* 32 1048576))]
            (recur tail (inc visited) (+ total (get record "bytes"))
                   (if (= relative "prepared-manifest.json") files (assoc files relative record)))))))))
(defn- cache-hit! [^Path directory key inputs]
  (require! (and (not (Files/isSymbolicLink directory)) (Files/isDirectory directory no-links)) "ArtifactConflict" {})
  (let [manifest (#'compiler/read-json! (.resolve directory "prepared-manifest.json") (* 4 1048576))]
    (require! (and (= "lean-local-compiled-modules/2" (get manifest "schema"))
                   (= key (get manifest "cacheKey")) (= inputs (get manifest "inputs"))
                   (= (get manifest "files") (inventory! directory))) "ArtifactConflict" {:cache-key key}) manifest))

(defn prepare!
  "Trusted helper configuration supplies independently reviewed source/binary pins.
   Captures only reachable modules and plans dependencies first. Returns preparation
   metadata, never runtime admission. No native reference/main is executed."
  [compiler {:keys [project source-root roots helper helper-source helper-sha256 helper-source-sha256
                     typed-exporter typed-exporter-source typed-exporter-sha256 typed-exporter-source-sha256 compile?] :as configuration} journal]
  (#'compiler/guard-code!)
  (require! (= implementation-record (#'compiler/source-record! implementation-source))
            "NativeCompileFailed" {:stage :implementation-mutation})
  (require! (and (map? configuration)
                 (every? #{:project :source-root :roots :helper :helper-source :helper-sha256 :helper-source-sha256
                            :typed-exporter :typed-exporter-source :typed-exporter-sha256 :typed-exporter-source-sha256 :compile?}
                         (keys configuration))
                 (or (nil? compile?) (boolean? compile?))) "UnsupportedProjectConfig" {})
  (vector! roots 128 "UnsupportedProjectConfig")
  (doseq [root roots] (module-components root) (require! (not (init? root)) "ModulePathConflict" {:module root}))
  (require! (and (instance? clojure.lang.IAtom journal) (= {} @journal)) "UnsupportedProjectConfig" {})
  (let [state (#'compiler/issued compiler)]
    (locking (:lock state)
      (require! (identical? state (#'compiler/issued compiler)) "UnsupportedProjectConfig" {})
      (let [project (project-path! project)
            _ (require! (and (string? source-root) (<= 1 (utf8-size! source-root) 4096)
                                (not (str/includes? source-root "\\")) (not (str/includes? source-root (str (char 0)))) (or (= "." source-root)
                                (and (not (str/starts-with? source-root "/"))
                                     (every? #(and (seq %) (not (#{"." ".." ".lake" ".git"} %))) (str/split source-root #"/")))))
                        "UnsupportedProjectConfig" {})
            root (source-path! project source-root)
            _ (require! (Files/isDirectory root no-links) "UnsupportedProjectConfig" {:source-root source-root})
            helper (#'compiler/executable! helper)
            helper-source (#'compiler/path! helper-source)
            helper-record (#'compiler/file-record helper (* 256 1024 1024))
            source-record (#'compiler/file-record helper-source (* 2 1024 1024))
            _ (require! (and (= helper-sha256 (get helper-record "sha256"))
                             (= helper-source-sha256 (get source-record "sha256"))) "HeaderRejected" {:stage :helper-pin})
            exporter (when compile? (#'compiler/executable! typed-exporter))
            exporter-source (when compile? (#'compiler/path! typed-exporter-source))
            exporter-record (when compile? (#'compiler/file-record exporter (* 256 1024 1024)))
            exporter-source-record (when compile? (#'compiler/file-record exporter-source (* 2 1024 1024)))
            _ (when compile?
                (require! (and (= typed-exporter-sha256 (get exporter-record "sha256"))
                               (= typed-exporter-source-sha256 (get exporter-source-record "sha256")))
                          "NativeCompileFailed" {:stage :typed-exporter-pin}))
            stage (Files/createTempDirectory ^Path (:cache state) ".local-project-" attrs)
            copied (.resolve stage "project") build (.resolve stage "build")
            _ (Files/createDirectory copied attrs) _ (Files/createDirectory build attrs)
            env (#'compiler/environment state (str build ":" (.resolve ^Path (:sysroot state) "lib/lean")))
            execution (assoc state :working-directory copied)]
        (swap! journal assoc :status :capturing :stage-directory (str stage) :processes [])
        (try
          (let [toolchain (#'compiler/toolchain! state journal stage)
                modules
                (loop [pending roots found {} paths {} total 0 edges 0]
                  (require! (and (<= (count found) 128) (<= (count pending) 2048)
                                 (<= total (* 16 1048576)) (<= edges 2048)) "BuildResourceLimit" {})
                  (if (empty? pending) found
                    (let [name (first pending) pending (subvec pending 1)]
                      (if (contains? found name) (recur pending found paths total edges)
                        (let [_ (require! (< (count found) 128) "BuildResourceLimit" {})
                              source (capture! root copied name) relative (:relative source)
                              _ (require! (<= (+ total (get-in source [:record "bytes"])) (* 16 1048576)) "BuildResourceLimit" {})
                              folded (.toLowerCase ^String relative Locale/ROOT)
                              _ (require! (not (contains? paths folded)) "ModulePathConflict" {:module name :relative relative})
                              receipt (#'compiler/run-process! execution journal stage (str "header-" (count found))
                                        [helper "--header" (.resolve copied relative)] env)
                              raw (#'compiler/read-json! (.resolve stage (get receipt "stdout")) 1048576)
                              imports (admit-header! raw source (.resolve copied relative))
                              deps (vec (distinct (keep #(let [n (get % "module")] (when-not (init? n) n)) imports)))
                              _ (doseq [dep deps] (require! (Files/isRegularFile (source-path! root (module-relative dep)) no-links)
                                                                         "ExternalImport" {:module name :import dep}))]
                          (recur (into pending deps)
                                 (assoc found name (assoc source :imports imports :dependencies deps :header receipt))
                                 (assoc paths folded name) (+ total (get-in source [:record "bytes"])) (+ edges (count deps))))))))
                order (dependency-order roots modules)
                inputs {"implementation" implementation-record "profile" profile "roots" roots "modules" (mapv #(dissoc (modules %) :header) order)
                        "toolchain" toolchain "helper" helper-record "helperSource" source-record
                        "typedExporter" exporter-record "typedExporterSource" exporter-source-record}
                inputs (json/read-str (String. ^bytes (#'compiler/canonical inputs) StandardCharsets/UTF_8))
                key (#'compiler/digest (#'compiler/canonical inputs))
                target (.resolve ^Path (:cache state) (str "local-modules-" key))
                hit (when (and compile? (Files/exists target no-links)) (cache-hit! target key inputs))
                compiled (if hit (get hit "compiled") (when compile?
                           (mapv (fn [index name]
                                   (let [m (get modules name)
                                         relative (str (subs (:relative m) 0 (- (count (:relative m)) 5)) ".olean")
                                         olean (.resolve build relative)
                                         _ (Files/createDirectories (.getParent olean) attrs)
                                         receipt (#'compiler/run-process! execution journal stage (str "module-" index)
                                                   [exporter "--source" (.resolve copied (:relative m)) "--olean" olean
                                                    "--local" "--typed-module" (json/write-str name)] env)
                                         [manifest rows] (#'compiler/read-stream! (.resolve stage (get receipt "stdout")))
                                         plan (get manifest "initializationPlan")]
                                     (require! (and (= name (get plan "module"))
                                                    (false? (get plan "moduleSystem"))
                                                    (= (mapv #(select-keys % ["module" "meta"])
                                                             (map #(hash-map "module" (get % "module") "meta" (get % "isMeta")) (:imports m)))
                                                       (get plan "imports"))
                                                    (every? #(and (true? (get % "sourceLocal")) (= name (get % "sourceModule"))) rows)
                                                    (= (count rows) (count (set (map #(get % "name") rows)))))
                                               "NativeCompileFailed" {:module name :stage :local-stream-provenance})
                                     {"module" name "source" (:record m) "olean" relative
                                      "oleanRecord" (#'compiler/file-record olean (* 32 1048576))
                                      "localStream" receipt "initializationPlan" plan "rowCount" (count rows)}))
                                 (range) order)))
                after (.resolve stage "identity-after")
                _ (Files/createDirectory after attrs)]
            (require! (= toolchain (#'compiler/toolchain! state journal (.resolve stage "identity-after"))) "NativeCompileFailed" {:stage :toolchain-mutation})
            (doseq [[name m] modules]
              (require! (= (:record m) (#'compiler/file-record (source-path! root (:relative m)) 1048576))
                        "NativeCompileFailed" {:module name :stage :source-mutation}))
            (require! (and (= helper-record (#'compiler/file-record helper (* 256 1048576)))
                           (= source-record (#'compiler/file-record helper-source (* 2 1048576)))
                           (or (not compile?)
                               (and (= exporter-record (#'compiler/file-record exporter (* 256 1048576)))
                                    (= exporter-source-record (#'compiler/file-record exporter-source (* 2 1048576))))))
                      "NativeCompileFailed" {:stage :producer-mutation})
            (require! (= implementation-record (#'compiler/source-record! implementation-source))
                      "NativeCompileFailed" {:stage :implementation-mutation})
            (when (and compile? (not hit))
              (#'compiler/write-json! (.resolve stage "prepared-manifest.json")
                                     {"schema" "lean-local-compiled-modules/2" "cacheKey" key "inputs" inputs
                                      "compiled" compiled "files" (inventory! stage)
                                      "runtimeReady" false "startupExecuted" false})
              (cache-hit! stage key inputs)
              (try (Files/move stage target (into-array java.nio.file.CopyOption [java.nio.file.StandardCopyOption/ATOMIC_MOVE]))
                   (catch java.nio.file.FileAlreadyExistsException _ (cache-hit! target key inputs))
                   (catch java.nio.file.DirectoryNotEmptyException _ (cache-hit! target key inputs)))
              (cache-hit! target key inputs))
            (swap! journal assoc :status (if compile? :modules-compiled :planned) :cache-key key :cache-hit (boolean hit))
            {:status (if compile? :modules-compiled :planned) :profile profile :cache-key key :directory (str (if compile? target stage)) :cache-hit (boolean hit) :order order :modules modules :inputs inputs
             :compiled compiled :runtime-ready false})
          (catch Throwable error (#'compiler/abort! journal error)))))))

(defn compile-modules!
  "Compiles exact captured DAG with the reviewed opt-in typed exporter. This is
   reusable compiler preparation; checked entries/startup/artifact issuing follow
   separately and no execution readiness is asserted."
  [compiler configuration journal]
  (prepare! compiler (assoc configuration :compile? true) journal))
