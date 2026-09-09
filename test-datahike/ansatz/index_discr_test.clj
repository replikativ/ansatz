(ns ansatz.index-discr-test
  "The CIC discrimination tree as a DURABLE datahike secondary index: external
   registration, the transactor's signed-delta feed, star-aware search, and — the point —
   that the index survives `connect` without being rebuilt."
  (:require [clojure.test :refer [deftest is testing]]
            [datahike.api :as d]
            [datahike.gc :as gc]
            [konserve.core :as k]
            [datahike.index.secondary :as sec]
            [datahike.index.entity-set :as es]
            [ansatz.index.discr :as dti]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn- nat [] (e/const' (name/from-string "Nat") []))
(defn- nle [a b]
  (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) (nat)
          (e/const' (name/from-string "instLENat") []) a b))
(defn- eqp [a b]
  (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) (nat) a b))
(defn- hole [] (e/mvar 900001))

(defn- bitset->set [bs]
  (set (es/entity-bitset-seq bs)))

(deftest direct-index-feed-and-search
  (testing "register + -transact feed + star-aware -search"
    (let [ix (reduce (fn [ix [eid c]]
                       (sec/-transact ix {:datom [eid :decl/dt-key (dti/conclusion-key c) 1]
                                          :added? true}))
                     (dti/make-index {:attrs [:decl/dt-key]} nil)
                     [[10 (nle (e/lit-nat 1) (e/lit-nat 2))]
                      [11 (nle (e/lit-nat 0) (hole))]      ; 0 ≤ *
                      [12 (eqp (e/lit-nat 3) (e/lit-nat 3))]])]
      (is (= #{10} (bitset->set (sec/-search ix {:query (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2)))} nil))))
      (is (= #{11} (bitset->set (sec/-search ix {:query (dti/query-key (nle (e/lit-nat 0) (e/lit-nat 7)))} nil)))
          "a stored star matches any subterm of the query")
      (is (= #{10 11} (bitset->set (sec/-search ix {:query (dti/query-key (nle (hole) (hole)))} nil)))
          "a query star matches every child")
      (is (= #{} (bitset->set (sec/-search ix {:query (dti/query-key (eqp (e/lit-nat 3) (e/lit-nat 4)))} nil))))
      (testing "retraction removes the entity"
        (let [ix' (sec/-transact ix {:datom [10 :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2))) 2]
                                     :added? false})]
          (is (= #{} (bitset->set (sec/-search ix' {:query (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2)))} nil)))))))))

(defn- fresh-cfg []
  {:store {:backend :memory :id (java.util.UUID/randomUUID)}
   :schema-flexibility :write :keep-history? false})

(defn- declare-schema! [conn]
  (d/transact conn [{:db/ident :decl/dt-key :db/valueType :db.type/string
                     :db/cardinality :db.cardinality/one}
                    {:db/ident :decl/name :db/valueType :db.type/string
                     :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}])
  (d/transact conn [{:db/ident :idx/dt
                     :db.secondary/type :ansatz.index/discr-tree
                     :db.secondary/attrs [:decl/dt-key]}]))

(defn- index-of [db] (get (:secondary-indices db) :idx/dt))

(deftest transactor-feeds-the-external-index
  (testing "declare the index in schema; datahike's transactor feeds it; structural queries resolve"
    (let [cfg (fresh-cfg)
          _ (d/create-database cfg)
          conn (d/connect cfg)]
      (try
        (declare-schema! conn)
        (d/transact conn [{:decl/name "le_a" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2)))}
                          {:decl/name "eq_a" :decl/dt-key (dti/conclusion-key (eqp (e/lit-nat 3) (e/lit-nat 3)))}])
        (let [db @conn
              ix (index-of db)
              eid (:db/id (d/pull db '[:db/id] [:decl/name "le_a"]))]
          (is (some? ix) "the index instance lives on the db")
          (is (= #{eid} (set (dti/search-eids ix (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2)))))))
          (is (= #{} (set (dti/search-eids ix (dti/query-key (nle (e/lit-nat 2) (e/lit-nat 1))))))))
        (finally (d/release conn))))))

(deftest index-survives-connect
  (testing "the trie is flushed at commit and RESTORED on connect — never rebuilt"
    (let [cfg (fresh-cfg)
          _ (d/create-database cfg)
          conn (d/connect cfg)
          le-key (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2)))]
      (declare-schema! conn)
      (d/transact conn [{:decl/name "le_a" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2)))}
                        {:decl/name "le_star" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 0) (hole)))}])
      (let [eid (:db/id (d/pull @conn '[:db/id] [:decl/name "le_a"]))
            flushed-root (:root @(index-of @conn))]
        (is (vector? flushed-root) "after commit the root is a persisted ref")
        (d/release conn)
        (let [conn2 (d/connect cfg)
              ix (index-of @conn2)]
          (try
            (is (some? ix))
            (is (= flushed-root (:root @ix)) "restored from the commit's key-map, not rebuilt")
            (is (= #{eid} (set (dti/search-eids ix le-key))) "a query on the restored index walks persisted nodes")
            (testing "and keeps accepting transactions afterwards"
              (d/transact conn2 [{:decl/name "le_b" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 5) (e/lit-nat 6)))}])
              (let [eid-b (:db/id (d/pull @conn2 '[:db/id] [:decl/name "le_b"]))]
                (is (= #{eid-b} (set (dti/search-eids (index-of @conn2) (dti/query-key (nle (e/lit-nat 5) (e/lit-nat 6)))))))
                (is (= #{eid} (set (dti/search-eids (index-of @conn2) le-key))) "earlier entries still present")))
            (finally (d/release conn2))))))))

(deftest gc-mark-lists-every-node
  (testing "-sec-mark and mark-from-key-map agree, and GC keeps live chunks while reclaiming superseded ones"
    (let [cfg (fresh-cfg)
          _ (d/create-database cfg)
          conn (d/connect cfg)]
      (try
        (declare-schema! conn)
        (d/transact conn [{:decl/name "le_a" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 1) (e/lit-nat 2)))}])
        (let [ix (index-of @conn)
              store (:store @ix)
              root-1 (second (:root @ix))
              marks (sec/-sec-mark ix)
              key-map {:type :ansatz.index/discr-tree :root root-1}]
          (is (seq marks))
          (is (every? #(= :ansatz.index/discr-node (first %)) marks))
          (is (= marks (sec/mark-from-key-map key-map store))
              "GC's store-only mark sees exactly the chunks the instance sees")
          ;; a second commit supersedes the root chunk
          (d/transact conn [{:decl/name "le_b" :decl/dt-key (dti/conclusion-key (nle (e/lit-nat 5) (e/lit-nat 6)))}])
          (let [root-2 (second (:root @(index-of @conn)))]
            (is (not= root-1 root-2))
            (let [marks-2 (sec/mark-from-key-map {:type :ansatz.index/discr-tree :root root-2} store)]
              (is (contains? marks-2 (dti/node-key root-2)) "the live root is whitelisted")
              (is (not (contains? marks-2 (dti/node-key root-1)))
                  "the superseded root is NOT whitelisted — it is sweepable (whether a given
                   gc-storage! call deletes it is datahike's safe-point cutoff, not ours)"))
            (gc/gc-storage! conn (java.util.Date.))
            (is (k/exists? store (dti/node-key root-2) {:sync? true}) "live root survives GC")
            (is (= 2 (count (dti/search-eids (index-of @conn) (dti/query-key (nle (hole) (hole))))))
                "the index still answers after GC")))
        (finally (d/release conn))))))
