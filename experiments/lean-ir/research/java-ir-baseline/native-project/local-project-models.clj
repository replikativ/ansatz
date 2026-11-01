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
