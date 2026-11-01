(ns ansatz.lean.jvm.compiler.evidence
  "Actual native build receipt issuer. Definition load does not launch processes.
   Load once: issued receipt identities survive only in this namespace cohort."
  (:require [ansatz.lean.jvm.compiler.transport :as compiler]
            [ansatz.lean.jvm.compiler.local :as local]
            [clojure.data.json :as json])
  (:import [java.nio.file Path Files LinkOption]
           [java.nio.file.attribute FileAttribute]
           [java.nio.charset StandardCharsets]
           [java.math BigInteger]
           [java.util WeakHashMap]))
(deftype BuildReceipt [])
(defonce ^:private receipts (WeakHashMap.))
(defn- need [ok code facts] (when-not ok (throw (ex-info code (assoc facts :code code)))))
(defn- vector! [xs maximum] (need (and (vector? xs) (<= (count xs) maximum)) "BuildResourceLimit" {}) xs)
(defn- name! [name]
  (loop [n name depth 0 total 0]
    (need (and (vector? n) (< depth 128) (<= total 16384)) "EntryRejected" {:name name})
    (if (= n ["anonymous"]) name
      (do (need (= 3 (count n)) "EntryRejected" {:name name})
          (let [[kind parent leaf] n]
            (need (string? leaf) "EntryRejected" {:name name})
            (case kind
              "str" (need (<= (#'local/utf8-size! leaf) 4096) "EntryRejected" {:name name})
              "num" (need (and (<= 1 (count leaf) 20)
                                (every? #(<= (int \0) (int %) (int \9)) leaf)
                                (or (= leaf "0") (not= \0 (first leaf)))
                                (not (pos? (.compareTo (BigInteger. leaf) (BigInteger. "18446744073709551615")))))
                           "EntryRejected" {:name name})
              (need false "EntryRejected" {:name name}))
            (recur parent (inc depth) (+ total (count leaf))))))))
(defn- abi [row]
  (let [d (or (get-in row ["ir" "fdecl"]) (get-in row ["ir" "extern"]))]
    {"name" (get d "f") "xs" (get d "xs") "type" (get d "type")}))
(defn- charge-bytes! [counter amount]
  (need (and (integer? amount) (<= 0 amount (* 64 1048576))) "BuildResourceLimit" {:stage :producer-byte-admission})
  (let [next (+ @counter amount)]
    (need (<= next (* 64 1048576)) "BuildResourceLimit" {:stage :producer-byte-admission})
    (reset! counter next)))
(defn- charge-produced! [counter ^Path directory receipt]
  (charge-bytes! counter (+ (get-in receipt ["stdoutRecord" "bytes"])
                           (get-in receipt ["stderrRecord" "bytes"])
                           (get (#'compiler/file-record (.resolve directory (str (get receipt "label") ".receipt.json")) 1048576) "bytes"))))
(defn- read-produced! [^Path directory receipt maximum]
  (let [path (.resolve directory ^String (get receipt "stdout")) expected (get receipt "stdoutRecord")]
    (need (= expected (#'compiler/file-record path maximum)) "ArtifactConflict" {:stage :producer-output-mutation})
    (let [document (#'compiler/read-json! path maximum)]
      (need (= expected (#'compiler/file-record path maximum)) "ArtifactConflict" {:stage :producer-output-mutation})
      document)))
(defn- producer! [document schema producer]
  (need (and (= schema (get document "schema")) (= producer (get document "producer"))
             (= compiler/lean-pin (get document "leanCommit")) (= "4.33.1" (get document "leanVersion"))
             (= {"wordBits" 64 "target" "x86_64-unknown-linux-gnu"} (get document "runtimeProfile"))
             (false? (get document "dynamicClosureProven"))) "ArtifactConflict" {:stage :producer-profile}))
(defn- row-index [rows]
  (reduce (fn [out row]
            (let [n (name! (get row "name"))]
              (need (and (= "decl" (get row "kind")) (= n (get (abi row) "name"))) "ArtifactConflict" {:name n})
              (vector! (get row "dependencies") 16384)
              (doseq [dependency (get row "dependencies")] (name! dependency))
              (when-let [old (get out n)] (need (= old row) "ArtifactConflict" {:name n}))
              (need (or (contains? out n) (< (count out) 4096)) "BuildResourceLimit" {})
              (assoc out n row))) {} (vector! rows 65536)))
(defn- merge-source [index source-index]
  ;; Keep original source rows unchanged as canonical local rows. Additional
  ;; imported initializationAction observations remain in :imported-rows; an
  ;; absent old source-schema field is not an observed null or a fabricated fact.
  (reduce-kv
   (fn [out n row]
     (if-let [source (get source-index n)]
       (let [observed-role (get-in row ["runtime" "role"]) source-role (get-in source ["runtime" "role"])
             shared ["kind" "name" "ir" "dependencies" "redirect" "sourceModule"]]
         (need (and (= (select-keys row shared) (select-keys source shared))
                    (false? (get row "sourceLocal")) (true? (get source "sourceLocal"))
                    (contains? (get row "runtime") "initializer")
                    (contains? (get source "runtime") "initializer")
                    (= (get-in row ["runtime" "initializer"]) (get-in source ["runtime" "initializer"]))
                    (or (= observed-role source-role)
                        (and (= "value" observed-role) (#{"closed" "ground"} source-role))))
               "ArtifactConflict" {:name n :stage :source-imported-observation})
         (assoc out n source))
       (assoc out n row))) {} index))
(defn- static-closure! [index roots]
  (loop [pending (vec roots) selected {}]
    (need (and (<= (count pending) 32768) (<= (count selected) 4096)) "BuildResourceLimit" {})
    (if (empty? pending) selected
      (let [n (peek pending) pending (pop pending)]
        (if (contains? selected n) (recur pending selected)
          (let [row (get index n)]
            (need row "MissingDependency" {:name n})
            (recur (into pending (get row "dependencies")) (assoc selected n row))))))))
(defn- expected-type! [signature type]
  (let [constant #(vector "const" ["str" ["anonymous"] %] [])]
    (if (= signature "io-unit")
      (need (= ["app" (constant "IO") (constant "Unit")] type) "EntryRejected" {:stage :template})
      (let [base (constant (if (= signature "nat-to-nat") "Nat" "String"))]
        (need (and (vector? type) (= 5 (count type)) (= "forall" (first type))
                   (= "default" (nth type 2)) (= base (nth type 3)) (= base (nth type 4)))
              "EntryRejected" {:stage :template})))))
(defn- admit-entries! [root requests document modules source-index]
  (producer! document "lean-native-entry-evidence/1" "NativeEntryEvidence.exportEntries")
  (let [entries (vector! (get document "entries") 16)
        index (row-index (get document "declarations"))]
    (need (and (= root (get document "compiledModule"))
               (= (mapv #(get % "name") requests) (mapv #(get % "name") entries))
               (= (count entries) (count (set (map #(get % "name") entries))))) "EntryRejected" {:root root})
    (doseq [[request entry] (map vector requests entries)]
      (let [n (get entry "name") signature (get request "signature") owner (get entry "compiledModule")]
        (need (and (contains? modules owner) (#{"definition" "opaque"} (get entry "kind"))
                   (= [] (get entry "levelParams")) (= signature (get-in entry ["typeCheck" "signature"]))
                   (= "Lean.Meta.isDefEq" (get-in entry ["typeCheck" "algorithm"]))
                   (= "default" (get-in entry ["typeCheck" "transparency"]))
                   (vector? (get entry "actualType"))) "EntryRejected" {:name n})
        (expected-type! signature (get-in entry ["typeCheck" "expectedType"]))
        (doseq [role ["raw" "callable"]]
          (let [a (get entry role) row (get index (get a "name")) source (get source-index (get a "name"))]
            (need (and (= a (abi row)) (= owner (get row "sourceModule"))
                       source (= owner (get source "sourceModule")) (= (get row "ir") (get source "ir")))
                  "EntryRejected" {:name n :stage :original-callable})))
        (let [callable (get entry "callable") params (get callable "xs")]
          (need (and (= n (get-in entry ["raw" "name"]))
                     (#{"original-interpreter-boxed-lookup" "original-owned-raw"} (get entry "selection"))
                     (vector? params) (= 1 (count params)) (false? (get-in params [0 "borrow"]))
                     (#{"object" "tobject" "tagged"} (get-in params [0 "ty"]))
                     (#{"object" "tobject" "tagged"} (get callable "type"))) "EntryRejected" {:name n}))))
    {:entries entries :index index}))
(defn authenticated-build
  "Internal publisher seam. Only actual issued identity authenticates the payload;
   copying this descriptive immutable map never creates another receipt."
  [receipt]
  (need (= BuildReceipt (class receipt)) "ArtifactConflict" {:stage :receipt-identity})
  (locking receipts
    (or (.get receipts receipt) (throw (ex-info "Actual issued native build receipt required" {:code "ArtifactConflict"})))))

(def ^:private implementation-source (#'compiler/implementation-source! *file*))
(def ^:private implementation-record (#'compiler/source-record! implementation-source))
(defn- guard-source! []
  (need (= implementation-record (#'compiler/source-record! implementation-source))
        "ArtifactConflict" {:stage :issuer-source-mutation}))

(defn build!
  "Compile and collect actual checked-entry/ordinary-startup evidence. Neither a
   preexisting caller map nor an external accepted flag can issue a BuildReceipt.
   ENTRIES is a vector of {:root TypedModule :name TypedName :signature String}."
  [compiler project-configuration evidence-configuration entries journal]
  (guard-source!)
  (vector! entries 16)
  (need (seq entries) "EntryRejected" {})
  (doseq [{:keys [root name signature] :as e} entries]
    (need (and (= #{:root :name :signature} (set (keys e)))
               (#{"io-unit" "nat-to-nat" "string-to-string"} signature)) "EntryRejected" {})
    (local/module-components root) (name! name))
  (need (= (count entries) (count (set (map :name entries)))) "EntryRejected" {:stage :duplicate-request})
  (let [started (System/nanoTime)
        {:keys [entry-helper entry-helper-source entry-helper-sha256 entry-helper-source-sha256]} evidence-configuration
        _ (need (= #{:entry-helper :entry-helper-source :entry-helper-sha256 :entry-helper-source-sha256}
                   (set (keys evidence-configuration))) "UnsupportedProjectConfig" {})
        helper (#'compiler/executable! entry-helper) helper-source (#'compiler/path! entry-helper-source)
        helper-record (#'compiler/file-record helper (* 256 1048576))
        helper-source-record (#'compiler/file-record helper-source (* 2 1048576))
        _ (need (and (= entry-helper-sha256 (get helper-record "sha256"))
                     (= entry-helper-source-sha256 (get helper-source-record "sha256"))) "EntryRejected" {:stage :helper-pin})
        build (binding [local/*build-start-nanos* started]
                (local/compile-modules! compiler project-configuration journal))
        state (#'compiler/issued compiler)]
    (locking (:lock state)
      (need (identical? state (#'compiler/issued compiler)) "NativeCompileFailed" {:stage :closed-compiler})
      (let [state (assoc state :build-start-nanos started :max-build-nanos 600000000000)
            directory (#'compiler/path! (:directory build))
            manifest (.resolve directory "prepared-manifest.json")
            manifest-record (#'compiler/file-record manifest (* 4 1048576))
            validated-cache (#'local/cache-hit! directory (:cache-key build) (:inputs build))
            _ (need (= manifest-record (#'compiler/file-record manifest (* 4 1048576)))
                    "ArtifactConflict" {:stage :cache-manifest-mutation})
            files (get validated-cache "files")
            _ (need (= files (#'local/inventory! directory)) "ArtifactConflict" {:stage :cache-baseline-mutation})
            stage (Files/createTempDirectory ^Path (:cache state) ".project-evidence-" (make-array FileAttribute 0))
            env (#'compiler/environment state (str (.resolve directory "build") ":" (.resolve ^Path (:sysroot state) "lib/lean")))
            roots (get-in build [:inputs "roots"])
            _ (doseq [{:keys [root]} entries] (need (some #{root} roots) "EntryRejected" {:root root}))]
        (swap! journal assoc :status :collecting-project-evidence :evidence-directory (str stage))
        (try
          (let [toolchain (#'compiler/toolchain! state journal stage)
                _ (need (= toolchain (get-in build [:inputs "toolchain"])) "NativeCompileFailed" {:stage :toolchain-mutation})
                byte-budget (atom 0)
                _ (charge-bytes! byte-budget (+ (get manifest-record "bytes")
                                               (reduce + 0 (map #(get % "bytes") (concat (vals files) (vals (#'local/inventory! stage)))))))
                source-rows (vec (mapcat (fn [m]
                                          (second (#'compiler/read-stream! (.resolve directory (get-in m ["localStream" "stdout"])))))
                                        (:compiled build)))
                source-index (row-index source-rows)
                grouped (mapv (fn [root] [root (filterv #(= root (:root %)) entries)]) roots)
                documents
                (mapv (fn [index [root selected]]
                        (let [requests (mapv #(hash-map "name" (:name %) "signature" (:signature %)) selected)
                              request {"schema" "lean-native-entry-requests/1" "module" root "entries" requests}
                              path (.resolve stage (str "entries-" index ".request.json"))
                              request-bytes (alength ^bytes (#'compiler/canonical request))
                              _ (need (<= request-bytes 65536) "BuildResourceLimit" {})
                              _ (charge-bytes! byte-budget request-bytes)
                              _ (#'compiler/write-json! path request)
                              receipt (#'compiler/run-process! state journal stage (str "entries-" index) [helper "--entries" path] env)
                              _ (charge-produced! byte-budget stage receipt)
                              document (read-produced! stage receipt (* 16 1048576))
                              admitted (admit-entries! root requests document (:modules build) source-index)]
                          {:request request :receipt receipt :document document :admitted admitted}))
                      (range) (filterv #(seq (second %)) grouped))
                startup-request {"schema" "lean-native-startup-requests/1" "profile" "legacy-private-ordinary/1"
                                 "requestedImports" (mapv #(hash-map "module" % "importAll" false "isExported" true "isMeta" false) roots)}
                startup-path (.resolve stage "startup.request.json")
                startup-request-bytes (alength ^bytes (#'compiler/canonical startup-request))
                _ (need (<= startup-request-bytes 65536) "BuildResourceLimit" {:stage :startup-request-extent})
                _ (charge-bytes! byte-budget startup-request-bytes)
                _ (#'compiler/write-json! startup-path startup-request)
                startup-helper (#'compiler/executable! (:helper project-configuration))
                startup-receipt (#'compiler/run-process! state journal stage "startup" [startup-helper "--startup" startup-path] env)
                _ (charge-produced! byte-budget stage startup-receipt)
                startup (read-produced! stage startup-receipt (* 16 1048576))
                _ (producer! startup "lean-native-startup-evidence/1" "NativeStartupEvidence.exportStartup")
                _ (need (and (= startup-request (get startup "request"))
                             (= (get startup-request "requestedImports") (get startup "requestedImports")
                                (get-in startup ["actualHeader" "imports"]))
                             (= "legacy-private-ordinary/1" (get startup "profile"))
                             (false? (get-in startup ["actualHeader" "isModule"]))
                             (= "private" (get-in startup ["actualHeader" "globalLevel"]))
                             (<= (count (vector! (get startup "moduleOrder") 4096)) 4096))
                        "UnsupportedStartup" {:stage :actual-profile})
                imported (row-index (vec (concat (mapcat #(get-in % [:document "declarations"]) documents)
                                                 (get startup "declarations"))))
                reconciled (merge-source imported source-index)
                selected-entries (vec (mapcat #(get-in % [:admitted :entries]) documents))
                selected (static-closure! reconciled (concat (mapcat #(map (fn [role] (get-in % [role "name"])) ["raw" "callable"]) selected-entries)
                                                             (get startup "closureRoots")))
                after (.resolve stage "identity-after") _ (Files/createDirectory after (make-array FileAttribute 0))
                _ (need (= toolchain (#'compiler/toolchain! state journal after)) "NativeCompileFailed" {:stage :toolchain-mutation})
                _ (need (and (= manifest-record (#'compiler/file-record manifest (* 4 1048576)))
                             (= files (#'local/inventory! directory))
                             (= helper-record (#'compiler/file-record helper (* 256 1048576)))
                             (= helper-source-record (#'compiler/file-record helper-source (* 2 1048576)))
                             (= (get-in build [:inputs "helper"])
                                (#'compiler/file-record startup-helper (* 256 1048576)))
                             (= (get-in build [:inputs "helperSource"])
                                (#'compiler/file-record (#'compiler/path! (:helper-source project-configuration)) (* 2 1048576))))
                        "ArtifactConflict" {:stage :build-mutation})
                _ (guard-source!) _ (#'compiler/guard-code!) _ (#'compiler/check-build-deadline! state)
                evidence-files (#'local/inventory! stage)
                _ (doseq [receipt (conj (mapv :receipt documents) startup-receipt)]
                    (need (= (get receipt "stdoutRecord") (get evidence-files (get receipt "stdout")))
                          "ArtifactConflict" {:stage :producer-output-mutation}))
                _ (need (<= (+ (get manifest-record "bytes")
                                  (reduce + 0 (map #(get % "bytes") (concat (vals files) (vals evidence-files))))) (* 64 1048576))
                        "BuildResourceLimit" {:stage :complete-artifact-extent})
                payload {:implementation implementation-record :evidence-files evidence-files :profile "native-project-build-evidence/2" :manifest-sha256 (get manifest-record "sha256")
                         :module-cache-key (:cache-key build) :module-directory directory :build-inputs (:inputs build)
                         :module-files files :compiled-modules (:compiled build)
                         :evidence-directory stage :entry-helper helper-record :entry-helper-source helper-source-record
                         :entry-documents documents :startup startup :startup-receipt startup-receipt
                         :source-rows source-index :imported-rows imported :rows selected :entries selected-entries
                         :runtime-ready false :startup-executed false}
                _ (#'compiler/check-build-deadline! state)
                token (BuildReceipt.)]
            ;; No issuer record is published until all actual native processes,
            ;; file/cohort rechecks and complete static dependency admission finish.
            (locking receipts (.put receipts token payload))
            (swap! journal assoc :status :native-evidence-issued :entry-count (count selected-entries) :row-count (count selected))
            token)
          (catch Throwable error (#'compiler/abort! journal error)))))))
