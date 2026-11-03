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
   :local-modules [(module-name "Main") (module-name "Bindings") (module-name "HostInterop")] :installed-imports []})
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
        eligible (filter #(= "reference" (get % "hostBinding")) selected)]
    (is (= "lean-native-entry-evidence/4" (get document "schema")))
    (is (= 14 (count selected)))
    (is (= 7 (count eligible)))
    (is (every? #(#{"none" "reference" "foreign"} (get % "hostBinding")) selected))
    (is (every? #(= "pure" (get-in % ["typeCheck" "signature" "effect"])) eligible))
    (is (some #(zero? (get % "semanticArity")) eligible))
    (is (some #(= 3 (get % "semanticArity")) eligible))))

(deftest exact-versioned-metadata-and-effect-refusals
  (let [document (fixture)
        index (first (keep-indexed #(when (= "reference" (get %2 "hostBinding")) %1) (get document "entries")))]
    (is (some? (rejected (update-in document ["entries" index] dissoc "hostBinding"))))
    (is (= :host-binding-kind (:reason (rejected (assoc-in document ["entries" index "hostBinding"] "true")))))
    (is (= :host-binding-reference (:reason (rejected (assoc-in document ["entries" index "kind"] "opaque")))))
    (is (some? (rejected (assoc-in document ["request" "schema"] "lean-native-entry-requests/3"))))
    (let [v3 (-> document (assoc "schema" "lean-native-entry-evidence/3")
                 (assoc-in ["request" "schema"] "lean-native-entry-requests/3"))]
      (is (some? (rejected v3)))
      (is (= 14 (count (:entries (checked (update v3 "entries" #(mapv (fn [e] (dissoc e "hostBinding")) %))))))))))

(defn- foreign-fixture []
  (binding [*artifact* (str (io/file (.getParentFile (io/file *artifact*)) "foreign-ffi.zip"))]
    (fixture)))

(defn- raw-row-path [document entry-index]
  (let [name (get-in document ["entries" entry-index "raw" "name"])]
    ["declarations" (first (keep-indexed #(when (= name (get %2 "name")) %1)
                                          (get document "declarations")))]))

(deftest actual-foreign-signatures-and-closure
  (let [document (foreign-fixture) result (checked document) selected (:entries result)
        foreign (filter #(= "foreign" (get % "hostBinding")) selected)]
    (is (= 4 (count foreign)))
    (is (= #{"pure" "io"} (set (map #(get-in % ["typeCheck" "signature" "effect"]) foreign))))
    (is (some #(zero? (get % "semanticArity")) foreign))
    (is (some #(and (= "reference" (get % "hostBinding"))
                    (= "io" (get-in % ["typeCheck" "signature" "effect"]))) selected))
    (doseq [e foreign role ["raw" "callable"]]
      (is (contains? (:declarations result) (get-in e [role "name"]))))))

(deftest foreign-authority-requires-the-original-extern
  (let [document (foreign-fixture) row-path (raw-row-path document 0)
        declaration (get-in document (conj row-path "ir" "extern"))]
    ;; Flags cannot create foreign authority or remove a required implementation.
    (is (some? (rejected (assoc-in document ["entries" 0 "hostBinding"] "none"))))
    (is (some? (rejected (-> document
                            (assoc-in ["entries" 0 "hostBinding"] "reference")
                            (assoc-in ["entries" 0 "kind"] "definition")))))
    (is (some? (rejected (-> document
                            (assoc-in ["entries" 5 "hostBinding"] "foreign")
                            (assoc-in ["entries" 5 "kind"] "opaque")))))
    (is (some? (rejected (assoc-in document (conj row-path "ir")
                                   {"fdecl" (-> declaration (dissoc "ext")
                                                 (assoc "body" ["unreachable"]))}))))
    (doseq [[field value] [["fn" "lean_string_length"]
                          ["fn" "ansatz_jvm_bad-symbol"]
                          ["backend" (module-name "jvm")]]]
      (is (some? (rejected (assoc-in document
                                     (into row-path ["ir" "extern" "ext" "entries" 0 "standard" field]) value)))))
    (let [v3 (-> document (assoc "schema" "lean-native-entry-evidence/3")
                 (assoc-in ["request" "schema"] "lean-native-entry-requests/3"))]
      (is (some? (rejected v3)))
      (is (some? (rejected (update v3 "entries" #(mapv (fn [e] (dissoc e "hostBinding")) %))))))))

(deftest foreign-effect-and-lowering-cannot-be-relabelled
  (let [document (foreign-fixture) row-path (raw-row-path document 1)]
    (is (some? (rejected (assoc-in document ["entries" 3 "typeCheck" "signature" "effect"] "pure"))))
    (is (some? (rejected (assoc-in document ["entries" 0 "typeCheck" "signature" "effect"] "io"))))
    ;; Agreement between two ABI copies cannot replace actual type lowering.
    (is (some? (rejected (-> document
                            (assoc-in ["entries" 1 "raw" "xs" 1 "ty"] "uint16")
                            (assoc-in (into row-path ["ir" "extern" "xs" 1 "ty"]) "uint16")))))
    (is (some? (rejected (assoc-in document ["entries" 3 "argumentPlan" 1 "representation"] "host-object"))))))

(deftest old-and-new-helper-pins-select-distinct-cohorts
  (doseq [version [3 4] :let [cohort (get cohorts/cohorts version)]]
    (is (= version (cohorts/schema-for-pins! (:source cohort) (:binary cohort)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (cohorts/schema-for-pins! (get-in cohorts/cohorts [3 :source]) (get-in cohorts/cohorts [4 :binary])))))

(defn check!
  ([] (run-tests 'pure-binding-checks))
  ([file] (binding [*artifact* file] (check!))))
