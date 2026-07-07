;; Stage-2: a CIC discrimination-tree as an EXTERNAL datahike secondary index.
;; Validates external ISecondaryIndex registration, the transactor's signed-delta
;; feed, and star-aware µs structural lookup. Runs under :datahike:test.
(ns ansatz.index-discr-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.index.discr :as dti]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [datahike.api :as d]
            [datahike.index.secondary :as sec]
            [datahike.index.entity-set :as es]))

(def ^:private le0 (e/const' (nm/from-string "LE.le") [lvl/zero]))
(def ^:private inst (e/const' (nm/from-string "instLENat") []))
(def ^:private nat (e/const' (nm/from-string "Nat") []))
(def ^:private eq0 (e/const' (nm/from-string "Eq") [(lvl/succ lvl/zero)]))
(defn- nle [a b] (reduce e/app le0 [nat inst a b]))
(defn- eqp [a b] (reduce e/app eq0 [nat a b]))
(defn- bs-seq [bs] (sort (es/entity-bitset-seq bs)))

(deftest star-aware-search-in-isolation
  (testing "register + -transact feed + star-aware -search"
    (let [idx (reduce (fn [ix [eid c]]
                        (sec/-transact ix {:datom [eid :decl/dt-key (dti/conclusion-key c) 1]
                                           :added? true}))
                      (dti/make-index {:attrs [:decl/dt-key]} nil)
                      [[100 (nle (e/lit-nat 1) (e/lit-nat 2))]
                       [101 (eqp (e/lit-nat 3) (e/lit-nat 3))]
                       [102 (nle (e/lit-nat 5) (e/lit-nat 9))]])
          hits (fn [pat] (bs-seq (sec/-search idx {:query (dti/query-key pat)} nil)))]
      (is (= [100 102] (hits (nle (e/mvar 900) (e/mvar 901)))) "LE.le _ _ matches both le decls")
      (is (= [101] (hits (eqp (e/mvar 902) (e/mvar 903)))) "Eq _ _ matches the eq decl")
      (is (= [102] (hits (nle (e/lit-nat 5) (e/lit-nat 9)))) "exact literals match only the exact decl")
      (is (= 2 (sec/-estimate idx {:query (dti/query-key (nle (e/mvar 900) (e/mvar 901)))}))))))

(deftest registered-as-external-index-type
  (testing "the index type is in datahike's public registry"
    (is (contains? (set (sec/registered-types)) :ansatz.index/discr-tree))))

(deftest transactor-feeds-the-external-index
  (testing "declare the index in schema; datahike's transactor feeds it the
            datom stream; structural queries resolve to the right decls"
    (let [cfg {:store {:backend :memory :id (java.util.UUID/randomUUID)}
               :schema-flexibility :write :keep-history? false}
          _ (d/create-database cfg)
          conn (d/connect cfg)]
      (try
        (d/transact conn [{:db/ident :decl/dt-key :db/valueType :db.type/string
                           :db/cardinality :db.cardinality/one}
                          {:db/ident :decl/name :db/valueType :db.type/string
                           :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}])
        (d/transact conn [{:db/ident :idx/dt
                           :db.secondary/type :ansatz.index/discr-tree
                           :db.secondary/attrs [:decl/dt-key]}])
        (d/transact conn [{:decl/name "le_a" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2)))}
                          {:decl/name "eq_a" :decl/dt-key (dti/conclusion-key (eqp (e/lit-nat 3) (e/lit-nat 3)))}
                          {:decl/name "le_b" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 5) (e/lit-nat 9)))}])
        (Thread/sleep 500)
        (let [idx (get-in @conn [:secondary-indices :idx/dt])
              names (fn [pat] (set (map (fn [eid] (:decl/name (d/pull @conn [:decl/name] eid)))
                                        (es/entity-bitset-seq
                                         (sec/-search idx {:query (dti/query-key pat)} nil)))))]
          (is (some? idx) "transactor instantiated the external index from schema")
          (is (= #{"le_a" "le_b"} (names (nle (e/mvar 900) (e/mvar 901)))) "LE.le _ _")
          (is (= #{"eq_a"} (names (eqp (e/mvar 902) (e/mvar 903)))) "Eq _ _"))
        (finally (d/delete-database cfg))))))
