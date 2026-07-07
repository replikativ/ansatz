;; Stage-1 datahike integration: project the kernel env into a datahike DB,
;; recall type-directed candidates by conclusion-head + MePo relevance, and
;; drive the relational proof search with them — kernel-certified.
;; Runs only under the :datahike alias (needs datahike on the classpath):
;;   clj -M:datahike:test -n ansatz.datalog-test
(ns ansatz.datalog-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.datalog :as dl]
            [ansatz.rel :as r]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private env*
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)
(def ^:dynamic *db* nil)

(use-fixtures :once
  (fn [f]
    (let [env (or @env* (throw (ex-info "init-medium.ndjson not found" {})))]
      (binding [*env* env, *db* (dl/project-env env)] (f)))))

(deftest projection-and-head-recall
  (testing "conclusion-head recall returns the focused structural candidate set"
    (let [le (set (map second (dl/candidates-for-head *db* "Nat.le" 20)))]
      (is (contains? le "Nat.le.refl"))
      (is (contains? le "Nat.le.step")))))

(deftest mepo-relevance-recall
  (testing "MePo IDF-weighted overlap ranks relevant ≤-lemmas up"
    (let [cands (map second (dl/candidates-for-goal
                             *db* "LE.le" ["LE.le" "Nat" "instLENat"] 10))]
      (is (some #{"Nat.zero_le"} cands))
      (is (some #{"Nat.le_refl"} cands)))))

(deftest end-to-end-datahike-recall-to-certified-proof
  (testing "prove 0 ≤ k using ONLY datahike-recalled candidates, kernel-certified"
    (let [le0 (e/const' (nm/from-string "LE.le") [lvl/zero])
          instLENat (e/const' (nm/from-string "instLENat") [])
          nat (e/const' (nm/from-string "Nat") [])
          nle (fn [a b] (reduce e/app le0 [nat instLENat a b]))
          k (e/fvar 12)
          lctx (-> (red/empty-lctx) (red/lctx-add-local 12 "k" nat))
          cands (dl/candidates-for-goal *db* "LE.le" ["LE.le" "Nat" "instLENat"] 12)
          res (r/run 1 (r/state *env* :lctx lctx)
                     (r/fresh (nle (e/lit-nat 0) k)
                              (fn [pf]
                                (r/all (r/proveo pf cands 3)
                                       (fn [s] (r/unit (assoc s :pf pf)))))))
          s (first res)]
      (is (some? s) "found a proof from the recalled candidates")
      (is (:ok? (r/certify s (:pf s))) "kernel certifies the recalled-lemma proof"))))
