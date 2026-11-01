(ns ansatz.lean.jvm.artifact
  "Bounded portable native-project artifacts. Reading requires an independent
   expected manifest digest and performs no native/toolchain discovery."
  (:require [ansatz.lean.jvm.producer :as producer-pins] [clojure.data.json :as json] [clojure.java.io :as io] [clojure.string :as str]
            [ansatz.lean.jvm.entry :as checked-entry])
  (:import [java.io InputStream OutputStream FilterInputStream FilterOutputStream ByteArrayOutputStream]
           [java.nio.file Path Files LinkOption]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio ByteBuffer CharBuffer]
           [java.security MessageDigest DigestOutputStream]
           [java.util WeakHashMap Locale]
           [java.util.zip ZipInputStream ZipOutputStream ZipEntry]))
(def schema "lean-native-local-project/2")
(def max-bytes (* 64 1048576))
(def lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(deftype ArtifactReceipt [])
(defonce ^:private issued (WeakHashMap.))
(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(defn- need [ok code facts] (when-not ok (throw (ex-info code (assoc facts :code code)))))
(defn- vector! [v maximum] (need (and (vector? v) (<= (count v) maximum)) "BuildResourceLimit" {}) v)
(defn- hex [data] (apply str (map #(format "%02x" (bit-and 255 %)) data)))
(defn- sha [^bytes data] (hex (.digest (MessageDigest/getInstance "SHA-256") data)))
(defn- record [^bytes data] {"bytes" (alength data) "sha256" (sha data)})
(defn- digest! [value]
  (need (and (string? value) (= 64 (count value))
             (every? #(or (<= (int \0) (int %) (int \9)) (<= (int \a) (int %) (int \f))) value))
        "ArtifactConflict" {:stage :expected-manifest-digest}) value)
(defn- utf8! [^bytes data]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
                (ByteBuffer/wrap data))))
(defn- ordered [v]
  (cond (map? v) (into (sorted-map) (map (fn [[k x]] [(str k) (ordered x)]) v))
        (sequential? v) (mapv ordered v) :else v))
(defn- canonical [value] (.getBytes (json/write-str (ordered value)) StandardCharsets/UTF_8))
(defn- strict-json! [text]
  (need (and (string? text) (<= (count text) (* 32 1048576))) "BuildResourceLimit" {:stage :json-extent})
  (loop [characters (seq text) depth 0 quoted false escaped false]
    (need (<= 0 depth 256) "ArtifactConflict" {:stage :json-depth})
    (when-let [c (first characters)]
      (cond
        escaped (recur (next characters) depth quoted false)
        (and quoted (= c \\)) (recur (next characters) depth quoted true)
        (= (int c) 34) (recur (next characters) depth (not quoted) false)
        quoted (recur (next characters) depth quoted false)
        (contains? #{\{ \[} c) (recur (next characters) (inc depth) false false)
        (contains? #{\} \]} c) (recur (next characters) (dec depth) false false)
        :else (do (need (or (not (or (< (int c) 32) (Character/isWhitespace (int c))))
                            (contains? #{32 9 10 13} (int c))) "ArtifactConflict" {:stage :json-whitespace})
                  (recur (next characters) depth false false)))))
  (json/read-str text :extra-data-fn
    (fn [value ^java.io.Reader reader]
      (loop [read 0]
        (need (<= read (count text)) "BuildResourceLimit" {:stage :json-trailing-data})
        (let [c (.read reader)]
          (cond (= -1 c) value
                (contains? #{32 9 10 13} c) (recur (inc read))
                :else (throw (ex-info "Trailing non-whitespace after artifact JSON value" {:code "ArtifactConflict"}))))))))
(defn- json! [^bytes data maximum]
  (need (<= (alength data) maximum) "BuildResourceLimit" {}) (strict-json! (utf8! data)))
(defn- relative! [value]
  (need (and (string? value) (<= 1 (count value) 4096)
             (not (str/includes? value "\\")) (not (str/includes? value (str (char 0))))
             (not (str/starts-with? value "/"))
             (every? #(and (seq %) (not (#{"." ".."} %))) (str/split value #"/" -1)))
        "ArtifactConflict" {:stage :relative-path :path value}) value)
(defn- read-stream! [^InputStream input maximum]
  (let [out (ByteArrayOutputStream.) buffer (byte-array 65536)]
    (loop [total 0]
      (let [n (.read input buffer)]
        (cond (neg? n) (.toByteArray out)
              (zero? n) (let [one (.read input)]
                          (if (neg? one) (.toByteArray out)
                            (do (need (< total maximum) "BuildResourceLimit" {}) (.write out one) (recur (inc total)))))
              :else (do (need (<= (+ total n) maximum) "BuildResourceLimit" {})
                        (.write out buffer 0 n) (recur (+ total n))))))))
(defn- read-file! [^Path root relative maximum]
  (relative! relative)
  (let [p (.normalize (.resolve root ^String relative))]
    (need (.startsWith p root) "ArtifactConflict" {:path relative})
    (loop [part p]
      (need (and part (not (Files/isSymbolicLink part))) "ArtifactConflict" {:path relative})
      (when-not (= part root) (recur (.getParent part))))
    (need (and (Files/isRegularFile p no-links) (<= (Files/size p) maximum)) "ArtifactConflict" {:path relative})
    (with-open [input (Files/newInputStream p (into-array java.nio.file.OpenOption [LinkOption/NOFOLLOW_LINKS]))]
      (read-stream! input maximum))))
(defn- name! [name]
  (loop [n name depth 0 text 0]
    (need (and (vector? n) (< depth 128) (<= text 16384)) "ArtifactConflict" {:stage :typed-name})
    (if (= n ["anonymous"]) name
      (do (need (= 3 (count n)) "ArtifactConflict" {:stage :typed-name})
          (let [[tag parent leaf] n]
            (need (and (string? leaf) (<= (count leaf) 4096)) "ArtifactConflict" {:stage :typed-name})
            (.encode (doto (.newEncoder StandardCharsets/UTF_8) (.onMalformedInput CodingErrorAction/REPORT)
                       (.onUnmappableCharacter CodingErrorAction/REPORT)) (CharBuffer/wrap ^String leaf))
            (need (or (= "str" tag)
                      (and (= "num" tag) (<= 1 (count leaf) 20)
                           (every? #(<= (int \0) (int %) (int \9)) leaf)
                           (or (= leaf "0") (not= \0 (first leaf)))
                           (not (pos? (.compareTo (java.math.BigInteger. leaf) (java.math.BigInteger. "18446744073709551615"))))))
                  "ArtifactConflict" {:stage :typed-name})
            (recur parent (inc depth) (+ text (count leaf))))))))
(defn- module-relative! [name]
  (name! name)
  (loop [n name parts []]
    (if (= n ["anonymous"])
      (do (need (seq parts) "ArtifactConflict" {:stage :module-name})
          (str (str/join "/" (reverse parts)) ".lean"))
      (let [[tag parent leaf] n]
        (need (and (= "str" tag) (seq leaf) (not (#{"." ".."} leaf))
                   (not-any? #(or (= % \/) (= % \\) (= (int %) 0)) leaf))
              "ArtifactConflict" {:stage :module-name})
        (recur parent (conj parts leaf))))))
(defn- abi [row]
  (let [d (or (get-in row ["ir" "fdecl"]) (get-in row ["ir" "extern"]))]
    {"name" (get d "f") "xs" (get d "xs") "type" (get d "type")}))
(defn- index! [rows]
  (reduce (fn [out row]
            (let [n (name! (get row "name"))]
              (need (and (= "decl" (get row "kind")) (= n (get (abi row) "name"))
                         (not (contains? out n))) "ArtifactConflict" {:stage :canonical-row :name n})
              (doseq [d (vector! (get row "dependencies") 16384)] (name! d)) (assoc out n row)))
          {} (vector! rows 4096)))
(defn- producer! [document expected-schema producer]
  (need (and (= expected-schema (get document "schema")) (= producer (get document "producer"))
             (= lean-commit (get document "leanCommit")) (= "4.33.1" (get document "leanVersion"))
             (= {"wordBits" 64 "target" "x86_64-unknown-linux-gnu"} (get document "runtimeProfile"))
             (false? (get document "dynamicClosureProven"))) "ArtifactConflict" {:stage :producer-cohort}))
(defn- path-ref! [files reference]
  (let [path (relative! (get reference "path")) bytes (get files path)]
    (need (and bytes (= (dissoc reference "path") (record bytes))) "ArtifactConflict" {:stage :file-reference :path path}) bytes))
(defn- source-observations! [files modules]
  (reduce
   (fn [out module]
     (let [name (get module "name") relative (module-relative! name)
           _ (need (= (str "modules/project/" relative) (get-in module ["source" "path"]))
                   "ArtifactConflict" {:stage :source-path})
           _ (path-ref! files (get module "source"))
           _ (need (= (str "modules/build/" (subs relative 0 (- (count relative) 5)) ".olean")
                      (get-in module ["olean" "path"])) "ArtifactConflict" {:stage :olean-path})
           _ (path-ref! files (get module "olean"))
           lines (str/split-lines (utf8! (path-ref! files (get module "localStream"))))
           _ (need (<= 1 (count lines) 20001) "BuildResourceLimit" {})
           manifest (strict-json! (first lines))
           rows (mapv strict-json! (rest lines))
           plan (get manifest "initializationPlan")]
       (need (and (= "lean-ir-probe/1" (get manifest "schema")) (= "4.33.1" (get manifest "leanVersion"))
                  (= {"wordBits" 64 "target" "x86_64-unknown-linux-gnu"} (get manifest "runtimeProfile"))
                  (= name (get plan "module")) (false? (get plan "moduleSystem"))
                  (= (mapv #(hash-map "module" (get % "module") "meta" (get % "isMeta")) (get module "requestedImports"))
                     (get plan "imports"))) "ArtifactConflict" {:stage :local-stream})
       (reduce (fn [index row]
                 (let [n (get row "name")]
                   (need (and (= "decl" (get row "kind")) (true? (get row "sourceLocal"))
                              (= name (get row "sourceModule")) (not (contains? index n))
                              (< (count index) 4096)) "ArtifactConflict" {:stage :source-local-observation})
                   (name! n) (assoc index n row))) out rows))) {} modules))
(defn- merge-imported! [documents]
  (reduce (fn [out row]
            (let [n (name! (get row "name"))]
              (when-let [old (get out n)] (need (= old row) "ArtifactConflict" {:name n :stage :imported-observation}))
              (need (or (contains? out n) (< (count out) 4096)) "BuildResourceLimit" {}) (assoc out n row)))
          {} (mapcat #(vector! (get % "declarations") 2048) documents)))
(defn- validate! [manifest files]
  (need (and (= schema (get manifest "schema")) (= "legacy-local-init-v2" (get manifest "profile"))
             (= {"frontend" "official-native" "javaKernelChecked" false "hostedInitImported" false "startupExecutionReceipt" false}
                (get manifest "trust"))) "ArtifactConflict" {:stage :artifact-profile})
  (let [producer (get manifest "producer")
        entry-schema (try
                       (checked-entry/schema-for-pins! (get-in producer ["entryHelperSource" "sha256"])
                                                      (get-in producer ["entryHelper" "sha256"]))
                       (catch clojure.lang.ExceptionInfo _
                         (need false "ArtifactConflict" {:stage :supported-producer})))
        _ (need (and entry-schema (= lean-commit (get producer "leanCommit")) (= "4.33.1" (get producer "leanVersion"))
                     (= "x86_64-unknown-linux-gnu" (get producer "target")) (= 64 (get producer "wordBits"))
                     (producer-pins/supported? "startupHeader" (get-in producer ["startupHelperSource" "sha256"]) (get-in producer ["startupHelper" "sha256"]))
                     (producer-pins/supported? "typedSource" (get-in producer ["typedSourceExporterSource" "sha256"]) (get-in producer ["typedSourceExporter" "sha256"]))
                     (false? (get-in manifest ["code" "dynamicClosureProven"]))) "ArtifactConflict" {:stage :supported-producer})
        original-inputs (json! (path-ref! files (get-in manifest ["inputs" "originalBuildInputs"])) (* 4 1048576))
        _ (need (and (= (get original-inputs "helper") (get producer "startupHelper"))
                     (= (get original-inputs "helperSource") (get producer "startupHelperSource"))
                     (= (get original-inputs "typedExporter") (get producer "typedSourceExporter"))
                     (= (get original-inputs "typedExporterSource") (get producer "typedSourceExporterSource"))
                     (= (get original-inputs "implementation") (get producer "compiler"))
                     (= (get original-inputs "transportImplementation") (get producer "transport"))
                     (= (get original-inputs "roots") (get-in manifest ["inputs" "requestedRoots"])))
                "ArtifactConflict" {:stage :original-build-cohort})
        modules (vector! (get manifest "modules") 128)
        module-names (set (map #(name! (get % "name")) modules))
        _ (need (= (count modules) (count module-names)) "ArtifactConflict" {:stage :module-identity})
        _ (need (= (count modules) (count (get original-inputs "modules"))) "ArtifactConflict" {:stage :source-dag})
        _ (doseq [[module source] (map vector modules (get original-inputs "modules"))]
            (need (and (= (get module "name") (get source ":name"))
                       (= (dissoc (get module "source") "path") (get source ":record"))
                       (= (get module "requestedImports") (get source ":imports"))
                       (= (get module "directLocalDependencies") (get source ":dependencies")))
                  "ArtifactConflict" {:stage :source-dag}))
        source-index (source-observations! files modules)
        rows (json! (path-ref! files (get-in manifest ["code" "canonicalRows"])) (* 32 1048576))
        index (index! rows)
        startup (json! (path-ref! files (get-in manifest ["startupEvidence" "raw"])) (* 16 1048576))
        _ (producer! startup "lean-native-startup-evidence/1" "NativeStartupEvidence.exportStartup")
        roots (get-in manifest ["inputs" "requestedRoots"])
        _ (need (and (vector? roots) (<= 1 (count roots) 128) (every? module-names roots)
                     (= (mapv #(hash-map "module" % "importAll" false "isExported" true "isMeta" false) roots)
                        (get startup "requestedImports") (get-in startup ["actualHeader" "imports"]))
                     (= "legacy-private-ordinary/1" (get startup "profile"))
                     (false? (get-in startup ["actualHeader" "isModule"]))
                     (= "private" (get-in startup ["actualHeader" "globalLevel"]))) "UnsupportedStartup" {})
        documents (mapv (fn [e]
                          (let [d (json! (path-ref! files (get e "raw")) (* 16 1048576))
                                request (json! (path-ref! files (get e "request")) 65536)]
                            (need (= (get-in checked-entry/cohorts [entry-schema :evidence]) (get d "schema"))
                                  "EntryRejected" {:stage :entry-producer-version})
                            (checked-entry/validate-document! (get e "rootModule") request d)
                            {:document d :request request})) (vector! (get manifest "entryEvidence") 16))
        entries (vec (mapcat #(get-in % [:document "entries"]) documents))
        imported (merge-imported! (into [startup] (map :document documents)))]
    (need (and (<= 1 (count entries) 16) (= (count entries) (count (set (map #(get % "name") entries))))) "EntryRejected" {})
    (doseq [entry entries]
      (need (module-names (get entry "compiledModule")) "EntryRejected" {:stage :entry-module})
      (checked-entry/validate-rows! entry index))
    (doseq [[name row] index]
      (doseq [dep (get row "dependencies")] (need (contains? index dep) "MissingDependency" {:name dep}))
      (let [observed (get imported name)]
        (need observed "ArtifactConflict" {:name name :stage :missing-native-observation})
        (if (true? (get row "sourceLocal"))
          (need (and (= row (get source-index name)) (module-names (get row "sourceModule"))
                     (= (select-keys row ["kind" "name" "ir" "dependencies" "redirect" "sourceModule"])
                        (select-keys observed ["kind" "name" "ir" "dependencies" "redirect" "sourceModule"]))
                     (= (get-in row ["runtime" "initializer"]) (get-in observed ["runtime" "initializer"]))
                     (or (= (get-in row ["runtime" "role"]) (get-in observed ["runtime" "role"]))
                         (and (= "value" (get-in observed ["runtime" "role"]))
                              (#{"closed" "ground"} (get-in row ["runtime" "role"])))) )
                "ArtifactConflict" {:name name :stage :source-observation})
          (need (= row observed) "ArtifactConflict" {:name name :stage :imported-observation}))))
    (doseq [root (concat (get startup "closureRoots") (mapcat #(map (fn [role] (get-in % [role "name"])) ["raw" "callable"]) entries))]
      (need (contains? index root) "MissingDependency" {:name root}))
    {:profile schema :build-inputs original-inputs :module-cache-key (get-in manifest ["inputs" "moduleCacheKey"])
     :source-rows source-index :rows index :entries entries :startup startup :imported-rows imported
     :artifact-manifest manifest :runtime-ready false :startup-executed false}))

(defn- nonclosing-output [^OutputStream output]
  (proxy [OutputStream] []
    (write ([value] (.write output (int value))) ([buffer offset length] (.write output ^bytes buffer (int offset) (int length))))
    (flush [] (.flush output))
    (close [] (.flush output))))
(defn- bounded-input [^InputStream input maximum]
  (let [total (atom 0)
        charge (fn [n] (when (pos? n) (swap! total + n) (need (<= @total maximum) "BuildResourceLimit" {:stage :archive-input})))]
    (proxy [InputStream] []
      (read ([] (let [n (.read input)] (when-not (neg? n) (charge 1)) n))
            ([buffer offset length]
             (let [n (.read input ^bytes buffer (int offset) (int (min length (inc (- maximum @total)))))]
               (charge n) n)))
      (close [] nil))))
(defn- canonical-bounded [value maximum]
  (let [data (ByteArrayOutputStream.) total (atom 0)
        reserve! (fn [n]
                   (need (<= (+ @total n) maximum) "BuildResourceLimit" {:stage :canonical-output})
                   (swap! total + n))
        output (proxy [OutputStream] []
                 (write ([v] (reserve! 1) (.write data (int v)))
                        ([buffer offset length] (reserve! length) (.write data ^bytes buffer (int offset) (int length))))) ]
    (with-open [writer (java.io.OutputStreamWriter. output StandardCharsets/UTF_8)]
      (json/write (ordered value) writer))
    (.toByteArray data)))
(defn- file-ref [path data] (assoc (record data) "path" path))
(defn- source-authenticator [receipt]
  ;; The source compiler was necessarily loaded to issue its opaque receipt.
  ;; Reader load! never calls this function or loads either compiler namespace.
  (let [symbols ['ansatz.lean.jvm.compiler.evidence/authenticated-build
                 'native-project-build-evidence-v2/authenticated-build]
        accessors (keep resolve symbols)]
    (or (some (fn [accessor]
                (try (accessor receipt)
                     (catch clojure.lang.ExceptionInfo error
                       (when-not (= "ArtifactConflict" (:code (ex-data error))) (throw error)) nil))) accessors)
        (throw (ex-info "Actual source compiler BuildReceipt required for artifact export" {:code "ArtifactConflict"})))))
(defn- export-files! [payload]
  (let [files (atom (sorted-map)) folded (atom #{}) total (atom 0)
        add! (fn [path data]
               (relative! path)
               (let [lower (.toLowerCase ^String path Locale/ROOT) n (alength ^bytes data)]
                 (need (and (< (count @files) 4095) (not (contains? @folded lower))
                            (<= (+ @total n) max-bytes)) "BuildResourceLimit" {:stage :artifact-files})
                 (swap! total + n) (swap! folded conj lower) (swap! files assoc path data)))
        capture! (fn [prefix ^Path directory expected]
                   (doseq [[relative expected-record] expected]
                     (need (and (map? expected-record) (integer? (get expected-record "bytes"))
                                (<= 0 (get expected-record "bytes") (* 32 1048576))
                                (<= (+ @total (get expected-record "bytes")) max-bytes)) "BuildResourceLimit" {})
                     (let [data (read-file! directory relative (get expected-record "bytes"))]
                       (need (= expected-record (record data)) "ArtifactConflict" {:stage :source-snapshot :path relative})
                       (add! (str prefix relative) data))))]
    (capture! "modules/" (:module-directory payload) (:module-files payload))
    (let [data (read-file! (:module-directory payload) "prepared-manifest.json" (* 4 1048576))]
      (need (= (:manifest-sha256 payload) (sha data)) "ArtifactConflict" {:stage :source-manifest})
      (add! "modules/prepared-manifest.json" data))
    (capture! "evidence/" (:evidence-directory payload) (:evidence-files payload))
    (add! "provenance/build-inputs.json" (canonical-bounded (:build-inputs payload) (min (* 4 1048576) (- max-bytes @total))))
    (add! "program/rows.json" (canonical-bounded (vec (sort-by #(json/write-str (get % "name")) (vals (:rows payload))))
                                               (min (* 32 1048576) (- max-bytes @total))))
    @files))
(defn- build-manifest [payload files]
  (let [inputs (:build-inputs payload)
        descriptor (fn [path] (file-ref path (get files path)))
        modules (mapv (fn [source product]
                        (let [name (get source ":name") relative (module-relative! name)]
                          {"name" name "source" (descriptor (str "modules/project/" relative))
                           "requestedImports" (get source ":imports") "directLocalDependencies" (get source ":dependencies")
                           "olean" (descriptor (str "modules/build/" (get product "olean")))
                           "localStream" (descriptor (str "modules/" (get-in product ["localStream" "stdout"])))}))
                      (get inputs "modules") (:compiled-modules payload))
        entries (mapv (fn [document]
                        (let [label (get-in document [:receipt "label"])]
                          {"rootModule" (get-in document [:request "module"])
                           "request" (descriptor (str "evidence/" label ".request.json"))
                           "raw" (descriptor (str "evidence/" (get-in document [:receipt "stdout"])))})) (:entry-documents payload))]
    {"schema" schema "profile" "legacy-local-init-v2"
     "producer" {"leanCommit" lean-commit "leanVersion" "4.33.1" "target" "x86_64-unknown-linux-gnu" "wordBits" 64
                 "entryHelper" (:entry-helper payload) "entryHelperSource" (:entry-helper-source payload)
                 "startupHelper" (get inputs "helper") "startupHelperSource" (get inputs "helperSource")
                 "typedSourceExporter" (get inputs "typedExporter") "typedSourceExporterSource" (get inputs "typedExporterSource")
                 "orchestrator" (:implementation payload) "compiler" (get inputs "implementation")
                 "transport" (get inputs "transportImplementation")}
     "inputs" {"requestedRoots" (get inputs "roots") "moduleManifestSHA256" (:manifest-sha256 payload)
               "moduleCacheKey" (:module-cache-key payload) "originalBuildInputs" (descriptor "provenance/build-inputs.json")}
     "modules" modules "entryEvidence" entries
     "startupEvidence" {"raw" (descriptor (str "evidence/" (get-in payload [:startup-receipt "stdout"])))
                        "actualProfile" (get-in payload [:startup "profile"])}
     "code" {"canonicalRows" (descriptor "program/rows.json") "dynamicClosureProven" false}
     "files" (into (sorted-map) (map (fn [[path data]] [path (record data)]) files))
     "trust" {"frontend" "official-native" "javaKernelChecked" false "hostedInitImported" false "startupExecutionReceipt" false}}))
(defn export!
  "Write an actual issued native build as a manifest-last ZIP. Return the expected
   manifest digest for trusted application configuration. Caller owns OUTPUT;
   no engine/live ledger is serialized and source/main is never executed here."
  [receipt ^OutputStream output]
  (need (instance? OutputStream output) "ArtifactConflict" {:stage :output-stream})
  (let [payload (source-authenticator receipt) files (export-files! payload)
        manifest (build-manifest payload files) manifest-bytes (canonical-bounded manifest (* 4 1048576))
        _ (need (<= (+ (alength manifest-bytes) (reduce + 0 (map #(alength ^bytes %) (vals files)))) max-bytes)
                "BuildResourceLimit" {:stage :complete-artifact-extent})
        _ (validate! manifest files)
        hash (MessageDigest/getInstance "SHA-256")
        digest-output (DigestOutputStream. (nonclosing-output output) hash)]
    (with-open [archive (ZipOutputStream. digest-output StandardCharsets/UTF_8)]
      (doseq [[path data] (concat files [["manifest.json" manifest-bytes]])]
        (let [entry (doto (ZipEntry. ^String path) (.setTime 0))]
          (.putNextEntry archive entry) (.write archive ^bytes data 0 (alength ^bytes data)) (.closeEntry archive))))
    {:schema schema :manifest-sha256 (sha manifest-bytes) :archive-sha256 (hex (.digest hash))
     :files (inc (count files)) :runtime-ready false}))
(defn load!
  "Read a bounded artifact using an independently trusted expected MANIFEST hash.
   No compiler namespace/toolchain/native process is loaded or probed. Caller owns
   INPUT. A self-reported hash from this archive is not independent trust."
  [^InputStream input expected-manifest-sha256]
  (need (instance? InputStream input) "ArtifactConflict" {:stage :input-stream})
  (digest! expected-manifest-sha256)
  (let [{:keys [files manifest-data]}
        (with-open [archive (ZipInputStream. (bounded-input input (* 96 1048576)) StandardCharsets/UTF_8)]
          (loop [files (sorted-map) folded #{} total 0 manifest nil entries 0]
            (if-let [entry (.getNextEntry archive)]
              (let [path (relative! (.getName ^ZipEntry entry)) lower (.toLowerCase ^String path Locale/ROOT)
                    _ (need (and (not (.isDirectory ^ZipEntry entry)) (nil? manifest) (< entries 4096)
                                 (not (contains? folded lower))) "ArtifactConflict" {:stage :archive-file-set :path path})
                    maximum (min (if (= path "manifest.json") (* 4 1048576) (* 32 1048576)) (- max-bytes total))
                    size (.getSize ^ZipEntry entry)
                    _ (need (or (= -1 size) (<= 0 size maximum)) "BuildResourceLimit" {:stage :archive-entry})
                    data (read-stream! archive maximum) n (alength data)]
                (.closeEntry archive)
                (if (= path "manifest.json")
                  (recur files (conj folded lower) (+ total n) data (inc entries))
                  (recur (assoc files path data) (conj folded lower) (+ total n) nil (inc entries))))
              (do (need manifest "ArtifactConflict" {:stage :missing-manifest}) {:files files :manifest-data manifest}))))
        _ (need (= expected-manifest-sha256 (sha manifest-data)) "ArtifactConflict" {:stage :manifest-digest})
        manifest (json! manifest-data (* 4 1048576))
        _ (need (= (get manifest "files") (into (sorted-map) (map (fn [[path data]] [path (record data)]) files)))
                "ArtifactConflict" {:stage :complete-file-set})
        payload (assoc (validate! manifest files) :manifest-sha256 expected-manifest-sha256
                       :artifact-file-records (get manifest "files"))
        token (ArtifactReceipt.)]
    ;; Only immutable parsed facts/records survive. Caller byte[] or stream
    ;; aliases and native mutable journals never enter the issued payload.
    (locking issued (.put issued token payload)) token))
(defn authenticated-artifact
  "Internal publisher accessor. Maps or foreign equal/hash implementations cannot
   manufacture an actual artifact receipt; no raw guest values are exposed."
  [receipt]
  (need (= ArtifactReceipt (class receipt)) "ArtifactConflict" {:stage :artifact-identity})
  (locking issued
    (or (.get issued receipt) (throw (ex-info "Actual issued artifact receipt required" {:code "ArtifactConflict"})))))
