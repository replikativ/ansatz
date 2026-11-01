(ns native-local-project-models-v2
  "Pure structural models; synthetic headers are not native authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [native-local-project-v2 :as local]))
(defn- name-of [& parts] (reduce (fn [p s] ["str" p s]) ["anonymous"] parts))
(deftest structural-module-identities
  (is (= "A.B/C.lean" (local/module-relative (name-of "A.B" "C"))))
  (is (not= (local/module-relative (name-of "A.B")) (local/module-relative (name-of "A" "B")))))
(deftest rejects-numeric-paths-and-escapes
  (doseq [n [["num" ["anonymous"] "7"] ["anonymous"] (name-of "../A")
             (name-of "..") (name-of "A\\B") (name-of "A/B") (name-of ".git")
             (name-of (str "A" (char 0))) (name-of (str (char 0xD800)))]]
    (is (thrown? clojure.lang.ExceptionInfo (local/module-relative n)))))
(deftest stable-diamond-order-and-actual-cycle
  (let [a (name-of "A") b (name-of "B") c (name-of "C") d (name-of "D")
        graph {a {:dependencies [b c]} b {:dependencies [d]} c {:dependencies [d]} d {:dependencies []}}]
    (is (= [d b c a] (local/dependency-order [a] graph)))
    (is (= [d c b a] (local/dependency-order [c a] graph)))
    (try (local/dependency-order [a] (assoc-in graph [d :dependencies] [a]))
         (is false)
         (catch clojure.lang.ExceptionInfo e (is (= [a b d a] (:cycle (ex-data e))))))
    (is (thrown? clojure.lang.ExceptionInfo (local/dependency-order [a] (dissoc graph d))))))
(defn check! [] (run-tests 'native-local-project-models-v2))

(defn- header-model []
  (let [init (name-of "Init") ordinary #(hash-map "module" %1 "isMeta" %2 "isExported" true "importAll" false)
        implicit [(ordinary init false) (ordinary init true)] explicit [(ordinary (name-of "A") false)]]
    {"schema" "lean-project-header/2" "producer" "NativeStartupEvidence.exportHeader"
     "leanCommit" "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" "leanVersion" "4.33.1"
     "fileName" "copied/A.lean" "sourceUTF8Bytes" 32 "lineEndingNormalization" "disabled"
     "parserEndByte" 12 "parserHasErrors" false
     "header" {"isModule" false "hasPrelude" false "explicitImports" explicit
                "requestedImports" (into implicit explicit) "insertedImportPrefix" implicit
                "interpretation" "original-HeaderSyntax.imports-includeInit-false-and-true"}}))
(deftest original-header-provenance-is-required
  (let [h (header-model) source {:name (name-of "B") :record {"bytes" 32}} admit #(#'local/admit-header! % source "copied/A.lean")]
    (is (= 3 (count (admit h))))
    (doseq [changed [(assoc h "schema" "lean-project-header/1") (assoc h "sourceUTF8Bytes" 31)
                     (assoc h "parserEndByte" 33) (assoc h "parserEndByte" -1) (assoc h "parserHasErrors" true)
                     (assoc h "lineEndingNormalization" "enabled") (assoc h "fileName" "other-file")
                     (assoc-in h ["header" "hasPrelude"] true) (assoc-in h ["header" "isModule"] true)
                     (assoc-in h ["header" "explicitImports" 0 "isMeta"] true)
                     (assoc-in h ["header" "insertedImportPrefix"] [])
                     (assoc-in h ["header" "requestedImports"] [])]]
      (is (thrown? clojure.lang.ExceptionInfo (admit changed))))))
(deftest bounded-depth-is-checked-on-actual-graph
  (let [names (mapv #(name-of (str "M" %)) (range 67))
        graph (into {} (map-indexed (fn [i n] [n {:dependencies (if (< i 66) [(nth names (inc i))] [])}]) names))]
    (is (thrown? clojure.lang.ExceptionInfo (local/dependency-order [(first names)] graph)))))

(defn check-files!
  "Explicit workspace supplied by root. Owner-free real filesystem negative models."
  [directory]
  (let [attrs (make-array java.nio.file.attribute.FileAttribute 0)
        options (into-array java.nio.file.OpenOption [java.nio.file.StandardOpenOption/CREATE_NEW java.nio.file.StandardOpenOption/WRITE])
        root (java.nio.file.Files/createTempDirectory ^java.nio.file.Path directory "local-capture-model-" attrs)
        copied (java.nio.file.Files/createDirectory (.resolve root "copied") attrs)
        source (.resolve root "A.lean")
        write #(java.nio.file.Files/write %1 ^bytes %2 options)
        data (.getBytes "-- exact λ\r\n\uFEFF" java.nio.charset.StandardCharsets/UTF_8)]
    (write source data)
    (let [record (#'local/capture! root copied (name-of "A"))]
      (is (= (alength data) (get-in record [:record "bytes"])))
      (is (java.util.Arrays/equals ^bytes data (java.nio.file.Files/readAllBytes (.resolve copied "A.lean")))))
    (java.nio.file.Files/delete source)
    (write source (.getBytes "changed" java.nio.charset.StandardCharsets/UTF_8))
    (is (java.util.Arrays/equals ^bytes data (java.nio.file.Files/readAllBytes (.resolve copied "A.lean"))))
    (let [link (.resolve root "linked-project")]
      (java.nio.file.Files/createSymbolicLink link copied attrs)
      (is (thrown? clojure.lang.ExceptionInfo (#'local/project-path! link))))
    (let [link (.resolve root "B.lean")]
      (java.nio.file.Files/createSymbolicLink link source attrs)
      (is (thrown? clojure.lang.ExceptionInfo (#'local/capture! root copied (name-of "B")))))
    (write (.resolve root "Malformed.lean") (byte-array [(unchecked-byte 255)]))
    (is (thrown? java.nio.charset.CharacterCodingException (#'local/capture! root copied (name-of "Malformed"))))
    (write (.resolve root "Huge.lean") (byte-array 1048577))
    (is (thrown? clojure.lang.ExceptionInfo (#'local/capture! root copied (name-of "Huge"))))
    {:workspace (str root) :assertions 7}))

(defn check-cache-files!
  "Synthetic theorem-only stream models validate cache semantics, not native proof."
  [directory]
  (let [attrs (make-array java.nio.file.attribute.FileAttribute 0)
        root (java.nio.file.Files/createTempDirectory ^java.nio.file.Path directory "local-cache-model-" attrs)
        write (fn [relative bytes]
                (let [path (.resolve root ^String relative)]
                  (java.nio.file.Files/createDirectories (.getParent path) attrs)
                  (java.nio.file.Files/write path ^bytes bytes
                    (into-array java.nio.file.OpenOption [java.nio.file.StandardOpenOption/CREATE_NEW java.nio.file.StandardOpenOption/WRITE])) path))
        record #(#'native-project-compiler-v1/file-record % (* 32 1048576))
        bytes #(.getBytes ^String % java.nio.charset.StandardCharsets/UTF_8)
        name (name-of "A")
        source (record (write "project/A.lean" (bytes "-- synthetic theorem-only source\n")))
        olean (record (write "build/A.olean" (bytes "synthetic module product; NOT native evidence")))
        imports [{"module" (name-of "Init") "isMeta" false "importAll" false "isExported" true}
                 {"module" (name-of "Init") "isMeta" true "importAll" false "isExported" true}]
        plan {"module" name "moduleSystem" false "imports" (mapv #(hash-map "module" (get % "module") "meta" (get % "isMeta")) imports) "actions" []}
        stream {"schema" "lean-ir-probe/1" "leanVersion" "4.33.1"
                "runtimeProfile" {"target" "x86_64-unknown-linux-gnu" "wordBits" 64} "initializationPlan" plan}
        stdout (record (write "module-0.jsonl" (bytes (str (clojure.data.json/write-str stream) "\n"))))
        stderr (record (write "module-0.stderr" (bytes "")))
        receipt {"label" "module-0" "exit" 0 "stdout" "module-0.jsonl" "stderr" "module-0.stderr"
                 "stdoutRecord" stdout "stderrRecord" stderr}
        _ (#'native-project-compiler-v1/write-json! (.resolve root "module-0.receipt.json") receipt)
        product {"module" name "source" source "olean" "A.olean" "oleanRecord" olean
                 "localStream" receipt "rowCount" 0 "initializationPlan" plan}
        inputs {"modules" [{":name" name ":record" source ":imports" imports}]}
        files (#'local/inventory! root)
        validate #(#'local/validate-compiled! root inputs % files)]
    (is (= [product] (validate [product])))
    (doseq [bad [[] [product product] [(assoc product "module" (name-of "Other"))]
                 [(assoc product "source" {"bytes" 0 "sha256" "wrong"})]
                 [(assoc product "olean" "../A.olean")]
                 [(assoc product "oleanRecord" nil)]
                 [(assoc product "oleanRecord" {"bytes" 0 "sha256" "wrong"})]
                 [(assoc-in product ["localStream" "stdout"] "../module-0.jsonl")]
                 [(assoc-in product ["localStream" "stdoutRecord"] {"bytes" 0 "sha256" "wrong"})]
                 [(assoc product "rowCount" 1)] [(assoc-in product ["initializationPlan" "module"] (name-of "Other"))]]]
      (is (thrown? clojure.lang.ExceptionInfo (validate bad))))
    (#'local/verify-files! root files)
    (java.nio.file.Files/write (.resolve root "project/A.lean") (bytes "mutated capture")
      (into-array java.nio.file.OpenOption [java.nio.file.StandardOpenOption/TRUNCATE_EXISTING java.nio.file.StandardOpenOption/WRITE]))
    (is (thrown? clojure.lang.ExceptionInfo (#'local/verify-files! root files))))
  {:assertions 13})

(deftest aggregate-deadline-refuses-before-native-effects
  (let [expired {:build-start-nanos (- (System/nanoTime) 600000000001) :max-build-nanos 600000000000}
        journal (atom {})]
    (is (nil? (#'native-project-compiler-v1/check-build-deadline! {})))
    (is (nil? (#'native-project-compiler-v1/check-build-deadline! {:build-start-nanos (System/nanoTime) :max-build-nanos 600000000000})))
    (is (thrown? clojure.lang.ExceptionInfo (#'native-project-compiler-v1/check-build-deadline! expired)))
    (is (thrown? clojure.lang.ExceptionInfo (#'native-project-compiler-v1/run-process! expired journal nil "must-not-start" [] {})))
    (is (= {} @journal))))
