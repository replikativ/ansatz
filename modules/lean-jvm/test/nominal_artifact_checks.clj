(ns ansatz-lean-jvm-nominal-artifact-checks
  "Pure native-free custody/retention checks. Synthetic bytes never issue authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.entry-v3 :as v3]
            [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm.publisher :as publisher]))
(defn- n [leaf] ["str" ["anonymous"] leaf])
(defn- products [module data]
  {"module" module "productSha256" (get (#'artifact/record data) "sha256")
   "products" (mapv (fn [role] (if (= role ".olean")
                                (merge {"role" role "present" true} (#'artifact/record data))
                                {"role" role "present" false})) installed/suffixes)})
(defn- manifest [rows] {"schema" "lean-jvm-used-module-products/1" "modules" rows})
(defn- check-products [baseline used files]
  (#'artifact/nominal-products!
   {"profile" "native-local-nominal-project-prepare/3" "compilationProducts" (manifest baseline)}
   [{"name" (n "App")}] [{:document {"moduleProducts" (manifest used)}}] files))
(deftest archived-local-role-bytes-and-absence-are-exact
  (let [data (.getBytes "local-product" "UTF-8") row (products (n "App") data)
        files {"modules/build/App.olean" data}]
    (is (nil? (check-products [] [row] files)))
    (is (thrown? Exception (check-products [] [row] {})))
    (is (thrown? Exception (check-products [] [row] (assoc files "modules/build/App.ir" data))))
    (is (thrown? Exception (check-products [] [row] {"modules/build/App.olean" (.getBytes "changed" "UTF-8")})))))
(deftest nonlocal-defining-products-require-compile-era-baseline
  (let [row (products (n "Init") (.getBytes "init-product" "UTF-8"))]
    (is (nil? (check-products [row] [row] {})))
    (is (thrown? Exception (check-products [] [row] {})))
    (is (thrown? Exception (check-products [row] [(assoc row "productSha256" (apply str (repeat 64 "0")))] {}))))
  (is (thrown? Exception (check-products [(products (n "Undeclared") (byte-array 0))] [] {}))))
(deftest compact-entry-retains-only-indexed-typed-metadata
  (let [typed {"group" 2 "arguments" [0 1] "result" 2 "effect" "pure"}
        compact (#'startup/compact-entry {"name" (n "entry") "typedStorage" typed
                                         "actualType" ["sensitive-native-ast"]
                                         "typeCheck" {"signature" (dissoc typed "group")}
                                         "arbitraryCompilerJournal" {"stage" "descriptive-test-marker"}})]
    (is (identical? typed (get compact "typedStorage")))
    (is (not (contains? compact "actualType")))
    (is (not (contains? compact "arbitraryCompilerJournal")))
    (is (= (dissoc typed "group") (get-in compact ["typeCheck" "signature"])))))
(deftest custody-is-not-a-self-authenticated-map
  (doseq [custody [nil {} {:source-closure [] :source-closure-sha256 (apply str (repeat 64 "0"))
                          :build-receipt {} :build-receipt-sha256 (apply str (repeat 64 "0"))}]]
    (is (thrown? Exception (v3/validate-producer-custody! custody {} {})))))
(deftest receipt-measurements-have-a-separate-finite-number-grammar
  (is (= {"elapsedSeconds" 0.25} (#'v3/custody-data-bound! {"elapsedSeconds" 0.25} 1024)))
  (doseq [value [Double/NaN Double/POSITIVE_INFINITY Double/NEGATIVE_INFINITY 1/2]]
    (is (thrown? Exception (#'v3/custody-data-bound! {"elapsedSeconds" value} 1024))))
  (is (thrown? Exception (#'v3/data-bound! {"elapsedSeconds" 0.25} 1024))))
(def ^:dynamic *producer-receipt* "test/fixtures/nominal-entry-v3/producer-build-receipt.json")
(deftest actual-reviewed-producer-custody-is-pinned-and-tamper-evident
  (let [receipt (json/read-str (slurp *producer-receipt*)) cohort (get entry/cohorts 3)
        custody {:source-closure (get receipt "sourceClosure")
                 :source-closure-sha256 (:source-closure cohort)
                 :build-receipt receipt :build-receipt-sha256 (:build-receipt cohort)}
        helper (first (filter #(= "entry" (get % "path")) (get receipt "products")))
        helper (dissoc helper "path") source {"sha256" (:source cohort)}]
    (is (= (:build-receipt cohort) (#'artifact/sha (.getBytes (slurp *producer-receipt*) "UTF-8"))))
    (is (= (:build-receipt cohort) (#'v3/custody-sha receipt true)))
    (is (= custody (v3/validate-producer-custody! custody source helper)))
    (is (thrown? Exception (v3/validate-producer-custody!
                           (assoc-in custody [:source-closure 0 "sha256"] (apply str (repeat 64 "0"))) source helper)))
    (is (thrown? Exception (v3/validate-producer-custody!
                           (assoc-in custody [:build-receipt "status"] "caller-admitted") source helper)))))
(def ^:dynamic *entry-fixture* "test/fixtures/nominal-entry-v3/oracle-entry-evidence.json")
(deftest each-document-has-one-storage-group-and-entry-root-indices
  ;; Descriptive helper only: no receipt or Prepared is issued by this check.
  (let [doc (json/read-str (slurp *entry-fixture*))
        receipt (json/read-str (slurp *producer-receipt*)) cohort (get entry/cohorts 3)
        custody {:source-closure (get receipt "sourceClosure") :source-closure-sha256 (:source-closure cohort)
                 :build-receipt receipt :build-receipt-sha256 (:build-receipt cohort)}
        helper (dissoc (first (filter #(= "entry" (get % "path")) (get receipt "products"))) "path")
        locals (vec (distinct [(get doc "compiledModule") (n "NativeNominalFixtures") (n "NativeBuiltinWitnessFixtures")]))
        payload {:producer-custody custody :entry-helper helper :entry-helper-source {"sha256" (:source cohort)}
                 :build-inputs {"modules" (mapv #(hash-map ":name" %) locals)}
                 :entries (get doc "entries") :entry-documents [{:request (get doc "request") :document doc}]}
        index (into {} (map #(vector (get % "name") %) (get doc "declarations")))
        typed (#'publisher/typed-documents! payload index)]
    (is (= 1 (count (:typed-groups typed))))
    (is (= #{:logical :normalized :runtime-witnesses} (set (keys (first (:typed-groups typed))))))
    (is (= (get doc "runtimeWitnesses") (:runtime-witnesses (first (:typed-groups typed)))))
    (is (= (count (get doc "entries")) (count (:entries typed))))
    (doseq [[original compact] (map vector (get doc "entries") (:entries typed))]
      (is (= (assoc (get-in original ["typeCheck" "signature"]) "group" 0) (get compact "typedStorage")))
      (is (not (contains? (get compact "typedStorage") "logical"))))))
(defn check!
  ([] (run-tests 'ansatz-lean-jvm-nominal-artifact-checks))
  ([entry-evidence-path producer-receipt-path]
   (binding [*entry-fixture* entry-evidence-path *producer-receipt* producer-receipt-path]
     (check!))))
