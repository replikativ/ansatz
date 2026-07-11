;; Direction-2: kernel logic (defeq confirmation) INSIDE datahike datalog
;; clauses. One planned query does structural recall (disc-tree index) THEN
;; kernel is-def-eq confirmation. Two flavors: a pure predicate (applies?) and
;; the mctx-threading form (apply-lemma: mctx-in → per-row mctx-out).
;; Runs under :datahike:test (clj -M:datahike:test -d test-datahike).
(ns ansatz.datalog-confirm-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.index.discr :as dti]
            [ansatz.datalog.confirm :as cf]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as kenv]
            [datahike.api :as d]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private env*
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)
(use-fixtures :once
  (fn [f]
    (binding [*env* (or @env* (throw (ex-info "init-medium.ndjson not found" {})))]
      (f))))

(def ^:private le0 (e/const' (nm/from-string "LE.le") [lvl/zero]))
(def ^:private inst (e/const' (nm/from-string "instLENat") []))
(def ^:private nat (e/const' (nm/from-string "Nat") []))
(def ^:private ofnat (e/const' (nm/from-string "OfNat.ofNat") [lvl/zero]))
(defn- nle [a b] (reduce e/app le0 [nat inst a b]))
(defn- onat [n] (reduce e/app ofnat [nat (e/lit-nat n)
                                     (reduce e/app (e/const' (nm/from-string "instOfNatNat") [])
                                             [(e/lit-nat n)])]))
(defn- ty [n] (.type (kenv/lookup *env* (nm/from-string n))))

(deftest confirmation-predicate-agrees-with-defeq
  (testing "kernel confirmation: which lemmas apply to a goal, by defeq"
    (let [g05 (nle (onat 0) (onat 5))]
      (is (cf/applies? *env* nil g05 "Nat.zero_le") "0 ≤ n applies to 0 ≤ 5")
      (is (not (cf/applies? *env* nil g05 "Nat.le_refl")) "n ≤ n does NOT apply to 0 ≤ 5")
      (is (cf/applies? *env* nil (nle (onat 7) (onat 7)) "Nat.le_refl") "n ≤ n applies to 7 ≤ 7"))))

(defn- with-db [f]
  (let [cfg {:store {:backend :memory :id (java.util.UUID/randomUUID)}
             :schema-flexibility :write :keep-history? false}
        _ (d/create-database cfg)
        conn (d/connect cfg)]
    (try
      (d/transact conn [{:db/ident :decl/dt-key :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
                        {:db/ident :decl/name :db/valueType :db.type/string :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}])
      (d/transact conn [{:db/ident :idx/dt :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/dt-key]}])
      (d/transact conn [{:decl/name "Nat.zero_le" :decl/dt-key (dti/decl-key (ty "Nat.zero_le"))}
                        {:decl/name "Nat.le_refl" :decl/dt-key (dti/decl-key (ty "Nat.le_refl"))}])
      (Thread/sleep 500)
      (f conn)
      (finally (d/delete-database cfg)))))

(deftest recall-then-confirm-in-one-query
  (testing "ONE datalog query: disc-tree recall (over-approx) + defeq confirm (filter)"
    (with-db
      (fn [conn]
        (let [goal (nle (onat 0) (onat 5))
              gk (dti/query-key goal)
              recall (d/q '[:find ?n :in $ ?key :where
                            [(ansatz.index.discr/dt-match :idx/dt ?key) [[?d]]]
                            [?d :decl/name ?n]] @conn gk)
              confirmed (d/q '[:find ?name :in $ ?env ?goal ?key :where
                               [(ansatz.index.discr/dt-match :idx/dt ?key) [[?d]]]
                               [?d :decl/name ?name]
                               [(ansatz.datalog.confirm/applies? ?env nil ?goal ?name)]]
                             @conn *env* goal gk)]
          (is (= #{["Nat.zero_le"] ["Nat.le_refl"]} recall) "structural recall over-approximates")
          (is (= #{["Nat.zero_le"]} confirmed) "kernel defeq confirmation filters le_refl out"))))))

(deftest mctx-threading-confirmation
  (testing "apply-lemma threads the metacontext: each surviving row carries its
            forked+unified mctx as a value (rel adopts it without recomputing)"
    (with-db
      (fn [conn]
        (let [goal (nle (onat 0) (onat 5))
              gk (dti/query-key goal)
              rows (d/q '[:find ?name ?out-mctx :in $ ?env ?goal ?key :where
                          [(ansatz.index.discr/dt-match :idx/dt ?key) [[?d]]]
                          [?d :decl/name ?name]
                          [(ansatz.datalog.confirm/apply-lemma ?env nil ?goal ?name) ?out-mctx]]
                        @conn *env* goal gk)]
          (is (= #{"Nat.zero_le"} (set (map first rows))) "le_refl dropped (apply-lemma → nil)")
          (let [[_ mctx] (first rows)]
            (is (contains? mctx :expr-assignment) "the carried value is a real metacontext")
            (is (pos? (count (:expr-assignment mctx))) "and it holds the unification")))))))
