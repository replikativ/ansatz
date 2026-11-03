(ns pure-binding-checks
  "V4 correspondence models over a real native-prepared artifact. These pure
   checks do not authenticate caller maps or grant runtime binding authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.entry-v3 :as entry]
            [ansatz.lean.jvm.entry :as cohorts])
  (:import [java.util.zip ZipFile]
           [java.nio.file Files]
           [java.security MessageDigest]
           [java.nio.charset StandardCharsets]))

(def ^:dynamic *artifact* "consumer/resources/lean/pure-ffi.zip")
(defn- fixture []
  (with-open [archive (ZipFile. (io/file *artifact*))
              input (.getInputStream archive (.getEntry archive "evidence/entries-0.jsonl"))]
    (let [bytes (.readNBytes input (inc (* 16 1048576)))]
      (assert (<= (alength bytes) (* 16 1048576)))
      (json/read-str (String. bytes StandardCharsets/UTF_8)))))
(defn- module-name [s] ["str" ["anonymous"] s])
(defn- context [document]
  {:root (get document "compiledModule") :request (get document "request")
   :module-products (get document "moduleProducts")
   :local-modules [(module-name "Main") (module-name "Bindings")] :installed-imports []})
(defn- checked [document] (entry/validate-document! (context document) document))
(defn- rejected [document]
  (try (checked document) nil
       (catch clojure.lang.ExceptionInfo failure (ex-data failure))))

(deftest native-oracle-and-fixture-custody
  (let [directory (io/file (.getParentFile (io/file *artifact*)) "../../../test/fixtures/pure-ffi")
        provenance (json/read-str (slurp (io/file directory "provenance.json")))
        digest (fn [file]
                 (.formatHex (java.util.HexFormat/of)
                             (.digest (MessageDigest/getInstance "SHA-256") (Files/readAllBytes (.toPath (io/file file))))))]
    (is (= "4.33.1" (get provenance "leanVersion")))
    (is (= (get-in cohorts/cohorts [4 :binary]) (get-in provenance ["entryProducer" "binary"])))
    (is (= (get provenance "archiveSHA256") (digest *artifact*)))
    (doseq [[file expected] (get provenance "files")]
      (is (= expected (digest (io/file directory file)))))
    (is (= "7\n46\n43,true\n10,true\n9,true\n12\n18\n[1, 2, 3]\ntrue\nfalse\n"
           (slurp (io/file directory "native.stdout"))))))

(deftest native-binding-eligibility-is-explicit
  (let [document (fixture) result (checked document)
        selected (get result :entries)
        eligible (filter #(true? (get % "pureBinding")) selected)]
    (is (= "lean-native-entry-evidence/4" (get document "schema")))
    (is (= 14 (count selected)))
    (is (= 7 (count eligible)))
    (is (every? #(boolean? (get % "pureBinding")) selected))
    (is (every? #(= "pure" (get-in % ["typeCheck" "signature" "effect"])) eligible))
    (is (some #(zero? (get % "semanticArity")) eligible))
    (is (some #(= 3 (get % "semanticArity")) eligible))))

(deftest exact-versioned-metadata-and-effect-refusals
  (let [document (fixture)
        index (first (keep-indexed #(when (get %2 "pureBinding") %1) (get document "entries")))]
    (is (some? (rejected (update-in document ["entries" index] dissoc "pureBinding"))))
    (is (= :pure-binding-flag (:reason (rejected (assoc-in document ["entries" index "pureBinding"] "true")))))
    (is (= :pure-binding-effect (:reason (rejected (assoc-in document ["entries" index "kind"] "opaque")))))
    (is (some? (rejected (assoc-in document ["request" "schema"] "lean-native-entry-requests/3"))))
    (let [v3 (-> document (assoc "schema" "lean-native-entry-evidence/3")
                 (assoc-in ["request" "schema"] "lean-native-entry-requests/3"))]
      (is (some? (rejected v3)))
      (is (= 14 (count (:entries (checked (update v3 "entries" #(mapv (fn [e] (dissoc e "pureBinding")) %))))))))))

(deftest old-and-new-helper-pins-select-distinct-cohorts
  (doseq [version [3 4] :let [cohort (get cohorts/cohorts version)]]
    (is (= version (cohorts/schema-for-pins! (:source cohort) (:binary cohort)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (cohorts/schema-for-pins! (get-in cohorts/cohorts [3 :source]) (get-in cohorts/cohorts [4 :binary])))))

(defn check!
  ([] (run-tests 'pure-binding-checks))
  ([file] (binding [*artifact* file] (check!))))
