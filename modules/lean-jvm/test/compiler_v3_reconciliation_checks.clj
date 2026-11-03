(ns ansatz-lean-jvm-compiler-v3-reconciliation-checks
  "Private checks using genuine source-phase and imported-phase observations."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.compiler.evidence :as evidence]
            [ansatz.lean.jvm.compiler.transport :as transport])
  (:import [java.nio.file Path Files]))

(def ^:dynamic *document* nil)
(def ^:dynamic *source-rows* nil)
(defn- n [part] ["str" ["anonymous"] part])
(defn- context []
  {:root (get *document* "compiledModule") :request (get *document* "request")
   :module-products (get *document* "moduleProducts")
   :local-modules [(get *document* "compiledModule") (n "NativeNominalFixtures")
                   (n "NativeBuiltinWitnessFixtures")]
   :installed-imports []})
(defn- checked [rows]
  (#'evidence/reconcile-v3-description! (context) *document* rows))
(defn- failure [rows]
  (try (checked rows) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest real-phase-observations-match-without-creating-authority
  (let [result (checked *source-rows*) source (into {} (map #(vector (get % "name") %) *source-rows*))]
    (is (= :none (:authority result)))
    (is (= :checked-description-only (:scope result)))
    (is (= :matched-source-rows (:source-reconciliation result)))
    (is (true? (:native-defeq-requires-authenticated-producer result)))
    (is (= 163 (count (:declarations result))))
    (doseq [[name row] (:declarations result) :when (contains? source name)]
      ;; Exact original source rows win, including source-only metadata.
      (is (= (source name) row)))))

(deftest source-ownership-and-presence-are-required
  (is (= :missing-local-source-row (:stage (failure []))))
  (is (= :source-row-owner (:stage (failure (assoc-in *source-rows* [0 "sourceLocal"] false)))))
  (is (= :source-row-owner (:stage (failure (assoc-in *source-rows* [0 "sourceModule"] (n "Other")))))))

(deftest actual-callable-must-match-its-source-ir
  (let [name (get-in *document* ["entries" 0 "callable" "name"])
        index (first (keep-indexed #(when (= name (get %2 "name")) %1) *source-rows*))
        row (get *source-rows* index)
        kind (if (get-in row ["ir" "fdecl"]) "fdecl" "extern")]
    (is (some? index))
    (is (= :original-callable
           (:stage (failure (assoc-in *source-rows* [index "ir" kind "type"] "void")))))))

(deftest closure-rows-also-require-matching-observations
  (let [roots (set (mapcat #(map (fn [role] (get-in % [role "name"])) ["raw" "callable"])
                           (get *document* "entries")))
        observed (set (map #(get % "name") (get *document* "declarations")))
        index (first (keep-indexed #(when (and (observed (get %2 "name"))
                                             (not (roots (get %2 "name")))) %1) *source-rows*))]
    (is (some? index))
    (is (= :missing-local-source-row (:stage (failure (into (subvec *source-rows* 0 index)
                                                           (subvec *source-rows* (inc index)))))))
    (is (= :source-imported-observation
           (:stage (failure (assoc-in *source-rows* [index "dependencies"]
                                     (if (seq (get-in *source-rows* [index "dependencies"]))
                                       [] [(n "ChangedDependency")]))))))
    (is (= :source-imported-observation
           (:stage (failure (assoc-in *source-rows* [index "runtime" "initializer"] "changed")))))
    (is (= :source-imported-observation
           (:stage (failure (assoc-in *source-rows* [index "runtime" "role"] "changed")))))))

(defn check! [document-path source-stream-path]
  (let [path (Path/of document-path (make-array String 0))]
    (assert (<= (Files/size path) (* 16 1048576)))
    (binding [*document* (json/read-str (Files/readString path))
              *source-rows* (second (#'transport/read-stream!
                                      (Path/of source-stream-path (make-array String 0))))]
      (run-tests 'ansatz-lean-jvm-compiler-v3-reconciliation-checks))))
