;; Definitions only: no runtime/project/process opens on load. Native references
;; and source/artifact checks are separate explicit campaigns over the same root.
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io]
         '[clojure.edn :as edn] '[clojure.string :as str])
(import '[ansatz.lean.jvm HostServices ReadOnlyFiles] '[java.nio.file Path Files CopyOption]
        '[java.nio.file.attribute FileAttribute FileTime] '[java.util.concurrent TimeUnit] '[java.nio.charset StandardCharsets])
(def entries ["metadataFields" "cursorAndEmpty" "writeErrors" "missingFacts" "nulFacts"])
(def byte-class (class (byte-array 0)))
(defn normalize [value]
  (cond (= byte-class (class value)) (mapv #(bit-and 255 %) value)
        (vector? value) (mapv normalize value) :else value))
(defn demand! [ok facts] (when-not ok (throw (ex-info "Filesystem conformance differs" facts))))
(defn path [value] (.toPath (.getCanonicalFile (io/file (str value)))))
(defn unix-metadata [root file]
  (let [m (Files/readAttributes (.resolve ^Path root file) "unix:lastAccessTime,lastModifiedTime,size,nlink,mode"
            (make-array java.nio.file.LinkOption 0))
        time (fn [key] (let [instant (.toInstant ^FileTime (get m key))] [(.getEpochSecond instant) (.getNano instant)]))]
    [(time "lastAccessTime") [(time "lastModifiedTime") [(get m "size") [(long (get m "nlink"))
      (= 0100000 (bit-and 0170000 (int (get m "mode"))))]]]]))
(defn inputs! [root]
  (demand! (Files/notExists (.resolve ^Path root "filesystem-conformance-missing") (make-array java.nio.file.LinkOption 0))
    {:reason :missing-path-exists})
  (into {} (map (fn [file] [file (vec (Files/readAllBytes (.resolve ^Path root file)))]) ["first.txt" "binary.dat"])))
(defn value! [project entry & args]
  (let [result (apply lean/call project entry args)]
    (demand! (= ["" ""] [(:stdout result) (:stderr result)]) {:entry entry :reason :unexpected-output})
    (let [value (normalize (:value result))]
      (if (= entry "cursorAndEmpty") [(normalize (.getBytes ^String (first value) StandardCharsets/UTF_8)) (second value)] value))))
(defn check-project! [project root]
  (let [before (inputs! root) expected (unix-metadata root "first.txt")
        metadata (value! project "metadataFields" "first.txt")
        rows [["cursor-first" (value! project "cursorAndEmpty" "first.txt")]
              ["cursor-binary" (value! project "cursorAndEmpty" "binary.dat")]
              ["write-errors" (value! project "writeErrors" "first.txt")]
              ["missing" (value! project "missingFacts" "filesystem-conformance-missing")]
              ["nul" (value! project "nulFacts")]]]
    (demand! (= expected metadata) {:reason :live-metadata-projections :expected expected :actual metadata})
    (doseq [[_ [_ [_ tty]]] (take 2 rows)] (demand! (false? tty) {:reason :regular-file-tty}))
    (demand! (= [[9 true] [9 true]] (second (nth rows 2))) {:reason :invalid-argument-none-code9})
    (demand! (= [4294967294 2] (second (nth rows 3))) {:reason :uv-versus-errno})
    (demand! (= [[22 true] [22 true]] (second (nth rows 4))) {:reason :nul-code-path-details})
    (demand! (= before (inputs! root)) {:reason :file-content-changed})
    {:rows rows :metadata metadata}))
(defn source! [compiler source-directory new-artifact-path read-only-root]
  (let [root (path read-only-root) output (path new-artifact-path)
        config (.build (.files (HostServices/builder) (ReadOnlyFiles/root root)))
        options {:compiler compiler :root-module "Main" :entries entries}]
    (demand! (Files/notExists output (make-array java.nio.file.LinkOption 0)) {:reason :fresh-artifact})
    (io/make-parents (.toFile output))
    (with-open [runtime (lean/open config)]
      (let [source (with-open [p (lean/load-project runtime source-directory options)] (check-project! p root))
            artifact (with-open [out (Files/newOutputStream output (into-array java.nio.file.OpenOption
                                                       [java.nio.file.StandardOpenOption/CREATE_NEW java.nio.file.StandardOpenOption/WRITE]))]
                       (lean/prepare-project source-directory options out))
            loaded (with-open [in (io/input-stream (.toFile output))
                               p (lean/load-artifact runtime in (:manifest-sha256 artifact))] (check-project! p root))]
        (demand! (= (:rows source) (:rows loaded)) {:reason :source-artifact})
        {:status :filesystem-conformance-source-pass :groups {:source source :artifact loaded} :artifact artifact}))))
(defn native! [sysroot source-directory fresh-output-directory read-only-root]
  (let [output (path fresh-output-directory) source (path source-directory) root (path read-only-root) sysroot (path sysroot)]
    (demand! (Files/notExists output (make-array java.nio.file.LinkOption 0)) {:reason :fresh-native-directory})
    (Files/createDirectories output (make-array FileAttribute 0))
    (doseq [file ["Main.lean" "NativeOracle.lean"]] (Files/copy (.resolve source file) (.resolve output file) (make-array CopyOption 0)))
    (letfn [(run! [stage cwd args]
              (let [mem (Files/readString (Path/of "/proc/meminfo" (make-array String 0)))
                    available (some-> (re-find #"(?m)^MemAvailable:\s+(\d+)\s+kB$" mem) second Long/parseLong)
                    _ (demand! (and available (>= available (* 2 1024 1024))) {:code "NativePreflightResourceLimit" :available-kib available})
                    command (into ["/usr/bin/prlimit" "--cpu=60:60" "--core=0:0" "--" (str (.resolve sysroot "bin/lean")) "-j1" "-M512"] args)
                    stdout (.toFile (.resolve output (str stage ".stdout"))) stderr (.toFile (.resolve output (str stage ".stderr")))
                    builder (doto (ProcessBuilder. ^java.util.List command) (.directory (.toFile ^Path cwd))
                              (.redirectOutput stdout) (.redirectError stderr))
                    _ (.put (.environment builder) "LEAN_SYSROOT" (str sysroot))
                    _ (.put (.environment builder) "LEAN_PATH" (str output java.io.File/pathSeparator (.resolve sysroot "lib/lean")))
                    process (.start builder)]
                (when-not (.waitFor process 60 TimeUnit/SECONDS)
                  (.destroyForcibly process) (throw (ex-info "Native conformance timeout" {:stage stage})))
                (let [receipt {:command command :exit (.exitValue process) :stdout (slurp stdout) :stderr (slurp stderr)}]
                  (spit (.toFile (.resolve output (str stage ".edn"))) (pr-str receipt))
                  (demand! (and (zero? (:exit receipt)) (empty? (:stderr receipt))) {:stage stage :receipt receipt}) receipt)))]
      (run! "compile" output ["-o" "Main.olean" "Main.lean"])
      (let [before (inputs! root) reference (run! "oracle" root ["--run" (str (.resolve output "NativeOracle.lean"))
                                                          "first.txt" "binary.dat" "filesystem-conformance-missing"])
            rows (mapv (fn [line] (let [[label value] (str/split line #"\t" 2)] [label (edn/read-string value)]))
                       (str/split-lines (:stdout reference))) metadata (second (first rows))]
        (demand! (= "metadata" (ffirst rows)) {:reason :native-metadata-row})
        (demand! (= before (inputs! root)) {:reason :native-content-changed})
        {:status :filesystem-conformance-native-pass :rows (subvec rows 1) :metadata metadata}))))
(defn compare-native! [source native]
  (demand! (= :filesystem-conformance-source-pass (:status source)) {:reason :source-missing})
  (demand! (= :filesystem-conformance-native-pass (:status native)) {:reason :native-missing})
  (demand! (= #{:source :artifact} (set (keys (:groups source)))) {:reason :missing-jvm-group})
  (doseq [[group result] (:groups source)]
    (demand! (= (:rows native) (:rows result)) {:reason :native-jvm-difference :group group :native (:rows native) :jvm (:rows result)})
    (demand! (= (second (:metadata native)) (second (:metadata result))) {:reason :modified-size-links-kind :group group}))
  ;; atime may change between campaigns; live metadata was checked against JDK
  ;; within each JVM group. Keep native timestamps as independent observations.
  {:status :filesystem-conformance-differential-pass :cases (count (:rows native))
   :native-metadata (:metadata native) :jvm-metadata (mapv (comp :metadata val) (:groups source))})
