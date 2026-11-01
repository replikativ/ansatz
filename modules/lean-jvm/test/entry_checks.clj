(ns ansatz-lean-jvm-entry-checks
  "Actual native v1/v2 metadata and tampering models. These validators alone
   never authenticate source files or issue a runtime/build/artifact receipt."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [clojure.java.io :as io] [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.compiler.evidence :as evidence])
  (:import [java.util.zip ZipFile]
           [java.nio.file Path]
           [ansatz.lean.jvm ProjectOptions NativeCompilerOptions]))
(def ^:dynamic *module-root* ".")
(defn- fixture [path] (json/read-str (slurp (io/file *module-root* path))))
(defn- v2 [] (fixture "test/fixtures/general-entry-v2.json"))
(defn- request [] (fixture "test/fixtures/general-entry-v2.request.json"))
(defn- index [document] (into {} (map #(vector (get % "name") %) (get document "declarations"))))
(defn- rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn- legacy []
  (with-open [archive (ZipFile. (io/file *module-root* "consumer/resources/lean/interop.zip"))]
    (mapv (fn [path] (with-open [input (.getInputStream archive (.getEntry archive path))]
                      (json/read-str (slurp input))))
          ["evidence/entries-0.request.json" "evidence/entries-0.jsonl"])))
(deftest actual-v1-and-v2-observations-share-validation
  (let [document (v2) entries (get document "entries") rows (index document)]
    (is (= 13 (count entries)))
    (is (identical? entries (entry/validate-document! (get document "compiledModule") (request) document)))
    (is (every? #(identical? % (entry/validate-rows! % rows)) entries)))
  (let [[request document] (legacy) entries (get document "entries") rows (index document)]
    (is (= 3 (count (entry/validate-document! (get document "compiledModule") request document))))
    (is (every? #(identical? % (entry/validate-rows! % rows)) entries))
    (is (= {"arguments" [] "effect" "io" "result" {"kind" "unit"}}
           (entry/descriptor (last entries))))))
(deftest exact-v2-type-and-call-plan-facts-required
  (let [sample (first (get (v2) "entries"))]
    (doseq [changed [(assoc sample "semanticArity" 0) (assoc sample "runtimeArity" 0)
                     (assoc sample "argumentPlan" []) (assoc sample "resultABI" "raw-nullary-bool-uint8")
                     (assoc-in sample ["callable" "xs" 0 "borrow"] true)
                     (assoc-in sample ["callable" "xs"] [])
                     (assoc-in sample ["typeCheck" "expectedType"] [])
                     (assoc-in sample ["typeCheck" "signature" "result" "kind"] "unknown")
                     (assoc sample "kind" "theorem") (assoc sample "levelParams" [["anonymous"]])
                     (assoc sample "actualType" nil)]]
      (is (rejected? #(entry/validate! changed))))))
(deftest exact-required-constructor-witnesses-not-caller-tags
  (let [sample (first (get (v2) "entries")) families (get-in sample ["codecWitnesses" "families"])]
    (doseq [changed [(assoc-in sample ["codecWitnesses" "families"] [])
                     (assoc-in sample ["codecWitnesses" "families"] (conj families (first families)))
                     (assoc-in sample ["codecWitnesses" "families" 0 "ctorInfo"] {})
                     (assoc-in sample ["codecWitnesses" "families" 0 "constructors" 0 "ctorInfo" "cidx"] 1)
                     (assoc-in sample ["codecWitnesses" "families" 0 "constructors" 0 "fields" 0 "irType"] "object")
                     (assoc-in sample ["codecWitnesses" "families" 0 "trivialStructure"] true)
                     (assoc-in sample ["codecWitnesses" "accepted"] true)]]
      (is (rejected? #(entry/validate! changed))))))
(deftest producer-request-version-and-independent-pins-must-match
  (let [document (v2) request (request) root (get document "compiledModule")]
    (doseq [[request document] [[(assoc request "schema" "lean-native-entry-requests/1") document]
                                [request (assoc document "producer" "NativeEntryEvidence.exportEntries")]
                                [(assoc-in request ["entries" 0 "signature"] "auto") document]
                                [request (assoc document "compiledModule" ["anonymous"])]]]
      (is (rejected? #(entry/validate-document! root request document)))))
  (is (= 1 (entry/schema-for-pins! (get-in entry/cohorts [1 :source]) (get-in entry/cohorts [1 :binary]))))
  (is (= 2 (entry/schema-for-pins! (get-in entry/cohorts [2 :source]) (get-in entry/cohorts [2 :binary]))))
  (is (rejected? #(entry/schema-for-pins! (get-in entry/cohorts [2 :source]) (get-in entry/cohorts [1 :binary])))))
(deftest original-row-abi-and-module-identity-remain-required
  (let [document (v2) sample (first (get document "entries")) rows (index document)
        callable (get-in sample ["callable" "name"])]
    (is (rejected? #(entry/validate-rows! sample (dissoc rows callable))))
    (is (rejected? #(entry/validate-rows! sample (assoc-in rows [callable "ir" "fdecl" "type"] "uint8"))))
    (is (rejected? #(entry/validate-rows! sample (assoc-in rows [callable "sourceModule"] ["anonymous"]))))))
(deftest v1-auto-request-refused-before-compiler-or-path-access
  (let [journal (atom {}) root ["str" ["anonymous"] "Main"]]
    (try
      (evidence/build! nil {} {:entry-schema 1} [{:root root :name root :signature "auto"}] journal)
      (is false "v1 must refuse name-only discovery")
      (catch clojure.lang.ExceptionInfo error
        (is (= "UnsupportedSignature" (:code (ex-data error))))))
    (is (= {} @journal))))
(deftest explicit-selection-resource-bound-is-independent-of-arity
  (let [path (Path/of "." (make-array String 0))
        compiler (NativeCompilerOptions. path path path)
        builder #(ProjectOptions/builder compiler)]
    (is (= entry/max-selected-entries ProjectOptions/MAX_SELECTED_ENTRIES))
    (is (thrown? IllegalArgumentException (.build (builder))))
    (let [options (builder)]
      (doseq [i (range ProjectOptions/MAX_SELECTED_ENTRIES)] (.function options (str "f" i)))
      (is (= 1024 (count (.entries (.build options)))))
      (.function options "overflow")
      (is (thrown? IllegalArgumentException (.build options))))))
(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-entry-checks)))
