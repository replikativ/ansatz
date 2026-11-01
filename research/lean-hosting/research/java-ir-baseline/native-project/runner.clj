(ns native-project-entry-v1
  "Fixed unchanged FP Lean tutorial: trusted official native frontend compilation,
   canonical Java IR execution. No hosted frontend or Java kernel certificate."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [clojure.string :as str] [java-ir-baseline :as j])
  (:import [java.nio.file Path Files LinkOption] [java.nio.charset StandardCharsets]
           [java.security MessageDigest] [java.util WeakHashMap]))
(deftype Artifact [])
(deftype Run [])
(defonce ^:private artifacts (WeakHashMap.))
(defonce ^:private runs (WeakHashMap.))
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def exporter-pin "0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e")
(def execution-pin "6e5a4309c6135d9f45784e209e01eafb2c6b08874f9f27c757d4d0c9983c2a6d")
(def source-pins
  {"Greeting.Basic" "b186dbcbc8cd3f04b6f9d39f4f130996ee75093b3d0923a9ceda2e2b70220afb"
   "Greeting" "b23733091936f7b4318c98880382dc901d5ca5830870bd40bbaa1128cbc91ed2"
   "Main" "84b2361691c0d105c438b137563c447e36e38827aaa633707ca99d14c4d20316"})
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :native-tutorial-entry-v1}))))
(defn- sha [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))))
(defn- bytes! [^Path p limit]
  (need (and (Files/isRegularFile p (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
             (<= 0 (Files/size p) limit)) "Bounded ordinary artifact file required")
  (let [b (Files/readAllBytes p)] (need (<= (alength b) limit) "Artifact grew while reading") b))
(defn- text! [bytes]
  (let [s (String. ^bytes bytes StandardCharsets/UTF_8)]
    (need (java.util.Arrays/equals ^bytes bytes (.getBytes s StandardCharsets/UTF_8)) "Artifact is not exact UTF-8") s))
(defn- json! [text]
  ;; Bound recursive JSON parsing before invoking the library reader.
  (loop [characters (seq text) depth 0 quoted false escaped false]
    (need (<= 0 depth 256) "Artifact JSON nesting exceeds bound")
    (when-let [c (first characters)]
      (cond
        escaped (recur (next characters) depth quoted false)
        (and quoted (= c \\)) (recur (next characters) depth quoted true)
        (= (int c) 34) (recur (next characters) depth (not quoted) false)
        quoted (recur (next characters) depth quoted false)
        (contains? #{\{ \[} c) (recur (next characters) (inc depth) false false)
        (contains? #{\} \]} c) (recur (next characters) (dec depth) false false)
        :else (recur (next characters) depth false false))))
  (json/read-str text))
(defn- path! [^Path root relative]
  (need (and (string? relative) (<= 1 (count relative) 1024)) "Bounded relative artifact path required")
  (let [p (.resolve root relative) normalized (.normalize p)]
    (need (and (not (.isAbsolute (Path/of relative (make-array String 0))))
               (= p normalized) (.startsWith normalized root)
               (= normalized (.toRealPath normalized (make-array LinkOption 0)))) "Artifact path escapes root or uses a symlink")
    normalized))
(defn- read-stream! [bytes]
  (let [lines (str/split-lines (text! bytes))]
    (need (<= 1 (count lines) 1025) "Bounded native declaration stream required")
    (mapv (fn [line] (need (<= (count line) 1048576) "Native declaration line exceeds bound")
            {:raw line :row (json! line)}) lines)))
(defn- module-name [s]
  (reduce (fn [p leaf] ["str" p leaf]) ["anonymous"] (str/split s #"\.")))
(defn- label [name]
  (loop [n name out () depth 0]
    (need (< depth 128) "Native typed Name exceeds bound")
    (if (= ["anonymous"] n) (str/join "." out)
      (do (need (and (vector? n) (= 3 (count n)) (= "str" (first n)) (string? (nth n 2)))
                "First native tutorial profile requires string-only typed Names")
          (recur (second n) (conj out (nth n 2)) (inc depth))))))
(defn- issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual issued native artifact/Run required" {})))))
(defn prepare!
  "TRUSTED native-build importer. EXPECTED-MANIFEST-SHA is supplied by the actual
   pinned build service or an independently authenticated frozen receipt. A SHA
   is not a signature, kernel check or permission to relabel caller source."
  [basis directory expected-manifest-sha]
  (need (or (string? directory) (instance? Path directory)) "Artifact directory must be a String or Path")
  (let [root (.toRealPath (.toAbsolutePath (.toPath (io/file (str directory)))) (make-array LinkOption 0))
        manifest-bytes (bytes! (.resolve root "manifest.json") 1048576)
        _ (need (= expected-manifest-sha (sha manifest-bytes)) "Native build manifest pin differs")
        m (json! (text! manifest-bytes)) files (get m "files") modules (get m "orderedModules")
        _ (need (and (= "native-compiled-project/1" (get m "schema"))
                     (= lean-pin (get m "producerLeanCommit")) (= "4.33.1" (get m "producerLeanVersion"))
                     (= "x86_64-unknown-linux-gnu" (get m "target")) (= exporter-pin (get m "exporterSHA256"))
                     (map? files) (<= 1 (count files) 64)
                     (= ["Greeting.Basic" "Greeting" "Main"] (mapv #(get % "module") modules)))
                "Unknown native tutorial producer or module profile")
        _ (need (and (every? #(and (integer? (get % "bytes")) (<= 0 (get % "bytes") 16777216)) (vals files))
                     (<= (reduce + (map #(get % "bytes") (vals files))) 33554432)) "Aggregate declared artifact bytes exceed bound")
        captured (reduce-kv (fn [out path entry]
                              (let [bytes (bytes! (path! root path) 16777216)]
                                (need (and (= (alength bytes) (get entry "bytes")) (= (sha bytes) (get entry "sha256")))
                                      "Native artifact file bytes differ")
                                (assoc out path bytes))) {} files)
        _ (need (<= (reduce + (map #(alength ^bytes %) (vals captured))) 33554432) "Aggregate artifact bytes exceed bound")
        _ (doseq [module modules]
            (let [name (get module "module") local (read-stream! (get captured (get module "localStream")))
                  plan (get-in (first local) [:row "initializationPlan"])]
              (need (and (= (get source-pins name) (sha (get captured (get module "source"))))
                         (= (get module "sourceSHA256") (get source-pins name))
                         (= (get module "localStreamSHA256") (sha (get captured (get module "localStream"))))
                         (= (get module "oleanSHA256") (sha (get captured (get module "olean"))))
                         (= plan (get module "initPlan")) (= [] (get plan "actions"))
                         (= (module-name name) (get plan "module")) (= "lean-init-plan/1" (get plan "schema")))
                    "Native source bytes, module or actual initialization plan differs")))
        stream-bytes (get captured (get m "executionStream"))
        _ (need (= execution-pin (get m "executionStreamSHA256") (sha stream-bytes)) "Native execution stream differs")
        stream (read-stream! stream-bytes) exported (first stream) rows (subvec stream 1)
        _ (need (and (= "manifest" (get-in exported [:row "kind"])) (= 6 (count rows))) "Expected complete six-row tutorial entry closure")
        index (reduce (fn [out {:keys [row] :as record}]
                        (let [n (get row "name") k (label n) runtime (get row "runtime")]
                          (need (and (= "decl" (get row "kind")) (not (contains? out n))
                                     (contains? #{"ordinary" "closed" "ground" "value"} (get runtime "role"))
                                     (nil? (get runtime "initializer")) (nil? (get row "redirect")))
                                "Missing/duplicate/initialized/redirected native entry row")
                          (assoc out n (assoc record :label k)))) {} rows)
        _ (need (= (count index) (count (set (map :label (vals index))))) "Native typed Names collide at runtime label")
        _ (doseq [[_ {:keys [row]}] index dep (get row "dependencies")]
            (need (contains? index dep) "Native static dependency is absent"))
        _ (doseq [[_ {:keys [row]}] index :let [raw (get-in row ["ir" "extern"])] :when raw]
            (need (contains? #{(module-name "IO.getStdout") (module-name "String.push")} (get row "name"))
                  "Unreviewed native tutorial extern")
            (.invoke (.getMethod ^Class (:class basis) "validateExternAbi" (into-array Class [java.util.Map]))
                     nil (object-array [row])))
        base (j/prepare-host-program basis [] []) binding (j/source-binding base {"native-manifest-sha256" expected-manifest-sha})
        headers (into {} (map (fn [[n {:keys [raw row]}]] [n (j/declaration-header binding row (sha (.getBytes ^String raw "UTF-8")))]) index))
        registered (j/register-headers base (vec (vals headers)))
        prepared (reduce-kv (fn [ctx n {:keys [row]}]
                              (if (get-in row ["ir" "fdecl"])
                                (j/materialize-body ctx (get headers n) row (mapv headers (get row "dependencies"))) ctx)) registered index)
        entry (get headers (get m "entry"))
        _ (need (and (= (module-name "main") (get m "entry")) entry
                     (= ["void"] (vec (j/request-value entry "paramTypes")))
                     (= [false] (vec (j/request-value entry "borrowed"))) (= "object" (j/request-value entry "resultType")))
                "Selected typed-source main's original raw ABI differs")
        ctx (-> prepared (dissoc :task-runtime :profiling-policy) (assoc :explicit false :initializing false))
        token (Artifact.)]
    (locking artifacts (.put artifacts token {:ctx ctx :manifest-sha256 expected-manifest-sha :entry entry
                                               :source binding :manifest m :headers headers})) token))
(defn owner-packet [run] @(issued runs run))
(defn execute-io-unit!
  "Execute the fixed native-checked annotated main once on a fresh inactive
   engine. Raw ABI guards are not a generic Lean type proof. Synchronous close
   is valid for this callback-free native entry profile; failures retain Run."
  [artifact]
  (let [a (issued artifacts artifact) ctx (:ctx a) slot (object-array [nil :call-pending])
        holder (atom {:status :opening :ctx ctx :result-slot slot}) token (Run.)]
    (locking runs (.put runs token holder))
    (try
      (let [engine (j/machine ctx)]
        (swap! holder assoc :engine engine :status :calling)
        (let [value (j/call ctx engine "main" [0])]
          (aset slot 0 value) (aset slot 1 :owned)
          (need (.isInstance ^Class (:node-class ctx) value) "Native main did not return an IO result Node")
          (need (and (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) value))
                     (= [0] (vec (.get ^java.lang.reflect.Field (:fields ctx) value)))
                     (zero? (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value))))
                "Native main did not return actual IO.ok Unit")
          (let [stdout (.invoke (.getMethod ^Class (:class ctx) "capturedStdout" (make-array Class 0)) engine (object-array 0))
                stderr (.invoke (.getMethod ^Class (:class ctx) "capturedStderr" (make-array Class 0)) engine (object-array 0))]
            (aset slot 1 :release-pending) (j/release! ctx engine value) (aset slot 1 :released) (aset slot 0 nil)
            (swap! holder assoc :status :closing) (j/close! ctx engine)
            (let [receipt {:mode :official-native-frontend-java-ir-entry :manifest-sha256 (:manifest-sha256 a)
                           :entry-type-evidence :fixed-native-checked-main-source-annotation
                           :result :io-ok-unit :stdout stdout :stderr stderr
                           :native-reference-match (= stdout (get-in a [:manifest "nativeReference" "stdoutUTF8"]))
                           :engine :synchronous-closed :hosted-frontend false :java-kernel-checked false}]
              (reset! holder {:status :closed :receipt receipt}) receipt))))
      (catch Throwable cause
        (swap! holder assoc :status :failed)
        (throw (ex-info "Native project entry failed; preserve actual Run owner packet" {:run token} cause))))))
