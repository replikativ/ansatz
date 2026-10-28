(ns lean-compatibility-corpus-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [lean-compatibility-corpus :as corpus]))

(def ^:dynamic *basis* nil)
(defn raw [rows] (json/read-str (json/write-str rows)))

(deftest pinned-corpus-exposes-bounded-progress
  (let [report (corpus/audit *basis* "research/compatibility-corpus.edn")
        entries (into {} (map (juxt :id identity)) (:entries report))]
    (is (= 6 (count entries)))
    (doseq [[id count] [[:rbmap-computation 15] [:mcmc-compiler-descriptions 81]]]
      (let [inventory (:inventory (entries id))]
        (is (= count (:declarations inventory)))
        (is (empty? (:missing-static-dependencies inventory)))
        (is (zero? (:unsupported-extern-count inventory)))
        (is (nil? (:closure-preparation-error inventory)))))
    (let [inventory (:inventory (entries :rbmap-original-main))]
      (is (= 79 (:declarations inventory)))
      (is (= 26 (count (:externs inventory))))
      (is (= 11 (:unsupported-extern-count inventory)))
      (is (empty? (:missing-static-dependencies inventory)))
      (is (string? (:closure-preparation-error inventory)))
      (is (= 2 (:dynamic-application-sites inventory))))
    (doseq [id [:mcmc-finite-execution :mcmc-proof-bearing-imports :multi-file-io-example]]
      (is (nil? (:inventory (entries id))))
      (is (seq (:pending (entries id)))))
    (is (= "formal/Mcmc/Executable/Finite/CompilerIRInterpreter.lean"
           (get-in entries [:mcmc-finite-execution :source :path])))))

(deftest static-dependencies-come-from-bodies
  (let [rows [(c/decl "caller" [] "object"
                     (c/let-ir 1 "object" (c/fap "missing" []) (c/ret 1)))
              (c/object-constant "unrelated")]
        ;; Deliberately forge empty metadata and include an unrelated row.
        rows (raw (mapv #(assoc % :dependencies []) rows))
        inventory (corpus/inventory *basis* rows ["caller"])]
    (is (= ["missing"] (:missing-static-dependencies inventory)))
    (is (= 1 (:declarations inventory)))
    (is (= "Missing static declarations" (:closure-preparation-error inventory)))))

(deftest inventory-does-not-execute-and-reports-dynamic-sites
  (let [rows (raw [(c/decl "apply" [(c/p 1 "object") (c/p 2 "object")] "object"
                          (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
                   (c/decl "trap" [] "object" ["unreachable"])])
        inventory (corpus/inventory *basis* rows ["apply" "trap"])]
    (is (= 1 (:dynamic-application-sites inventory)))
    (is (= 2 (:declarations inventory)))
    (is (nil? (:closure-preparation-error inventory)))
    (is (seq (:limits inventory)))))

(deftest invalid-corpus-identities-fail-closed
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hash mismatch"
                       (corpus/audit-entry *basis*
                         {:id :tampered :source {:fixture {:path "test/fixtures/unchanged-programs/rbmap.lean"
                                                          :sha256 "wrong"}}})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate/ambiguous"
                       (corpus/inventory *basis* (raw [(c/object-constant "same")
                                                       (c/object-constant "same")]) ["same"]))))

(deftest producer-manifest-validation
  (let [entry {:id :synthetic :ir {:path "unused" :sha256 "unused"} :roots ["root"]}
        row (first (raw [(c/object-constant "root")]))]
    (with-redefs [corpus/sha256 (constantly "unused")]
      (doseq [rows [[row]
                    [{"kind" "manifest" "leanVersion" "4.33.1"}
                     {"kind" "manifest" "leanVersion" "4.33.1"} row]]]
        (with-redefs [j/rows (constantly rows)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exactly one manifest"
                               (corpus/audit-entry *basis* entry {:version "4.33.1"}))))))
    (with-redefs [corpus/sha256 (constantly "unused")
                  j/rows (constantly [{"kind" "manifest" "leanVersion" "0.0.0"} row])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"producer version mismatch"
                           (corpus/audit-entry *basis* entry {:version "4.33.1"}))))))

(deftest runtime-links-are-reported-without-claiming-acceptance
  (let [rows (raw [(assoc (c/object-constant "root")
                         :runtime {:initializer (c/name-ir "init")}
                         :redirect {:name (c/name-ir "redirect-target")})
                   (c/object-constant "init")
                   (c/object-constant "redirect-target")])
        inventory (corpus/inventory *basis* rows ["root"])]
    (is (= 3 (:declarations inventory)))
    (is (= [{:name "root" :initializer "init" :redirect "redirect-target"}]
           (:row-runtime-links inventory)))
    (is (nil? (:closure-preparation-error inventory)))
    (is (some #(re-find #"does not implement or validate row" %) (:limits inventory)))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'lean-compatibility-corpus-checks)))
