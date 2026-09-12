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

(deftest search-scored-orders-by-specificity
  (testing "Lean's DiscrTree specificity: a stored pattern that matched more CONCRETE keys
            outranks one matched only through stars — the order the durable index must return,
            because it over-approximates (a Mathlib goal recalls ~5,500 declarations)"
    (let [ix (reduce (fn [ix [eid c]]
                       (sec/-transact ix {:datom [eid :decl/dt-key (dti/conclusion-key c) 1]
                                          :added? true}))
                     (dti/make-index {:attrs [:decl/dt-key]} nil)
                     [[10 (nle (e/lit-nat 1) (e/lit-nat 2))]      ; fully concrete
                      [11 (nle (e/lit-nat 1) (hole))]             ; one star
                      [12 (nle (hole) (hole))]])                  ; both stars
          scored (dti/search-scored ix (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2))))]
      (is (= [10 11 12] (mapv first scored)) "most specific first")
      (is (apply > (mapv second scored)) "and strictly decreasing scores")
      (is (= (set (map first scored))
             (set (dti/search-eids ix (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2))))))
          "the same answers as the unscored search, only ordered")
      (testing "one entry per entity, carrying its BEST score"
        (let [ix' (sec/-transact ix {:datom [10 :decl/dt-key (dti/conclusion-key (nle (hole) (hole))) 2]
                                     :added? true})
              scored' (dti/search-scored ix' (dti/query-key (nle (e/lit-nat 1) (e/lit-nat 2))))]
          (is (= 1 (count (filter #(= 10 (first %)) scored'))))
          (is (= (second (first scored')) (second (first scored))) "the concrete match still wins"))))))

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

(defn- head-const [i] (e/const' (name/from-string (str "K" i)) []))

(deftest wide-node-persists-in-buckets
  (testing "a large node keeps its small children in sibling BUCKET chunks; lookups and
            star queries resolve through a restored skeleton; marks include the buckets"
    (binding [dti/chunk-max-values 3]
      (let [cfg (fresh-cfg)
            _ (d/create-database cfg)
            conn (d/connect cfg)
            store (:store @conn)]
        (try
          ;; 40 distinct head symbols, one lemma each → root n=40 > 3, every child small
          (let [ix (reduce (fn [ix i]
                             (sec/-transact ix {:datom [(+ 100 i) :decl/dt-key (dti/conclusion-key (head-const i)) 1]
                                                :added? true}))
                           (dti/make-index {:attrs [:decl/dt-key]} nil)
                           (range 40))
                key-map (sec/-sec-flush ix store "main")
                restored (sec/-sec-restore (dti/make-index {:attrs [:decl/dt-key]} nil) store key-map)
                root-chunk (k/get store (dti/node-key (:root key-map)) nil {:sync? true})]
            (is (= :ansatz.index/discr-tree (:type key-map)))
            (is (pos? (count (:buckets root-chunk))) "the root chunk carries bucket addresses")
            (is (every? #(= :bref (first %)) (vals (:children root-chunk))) "small children live in buckets")
            (is (= #{117} (set (dti/search-eids restored (dti/query-key (head-const 17))))) "exact lookup through one bucket")
            (is (= (set (range 100 140)) (set (dti/search-eids restored [{:tag :star}]))) "a star at the root explores every bucket")
            (is (= #{} (set (dti/search-eids restored (dti/query-key (head-const 99))))))
            (let [marks (sec/-sec-mark restored)]
              (is (> (count marks) (count (:buckets root-chunk))) "marks cover root + buckets")
              (is (= marks (sec/mark-from-key-map key-map store))))
            (testing "a later insert rewrites the node and ONE bucket, keeps the others"
              (let [ix2 (sec/-transact restored {:datom [200 :decl/dt-key (dti/conclusion-key (head-const 5)) 2] :added? true})
                    key-map2 (sec/-sec-flush ix2 store "main")
                    root2 (k/get store (dti/node-key (:root key-map2)) nil {:sync? true})
                    changed (count (filter (fn [[i a]] (not= a (get (:buckets root-chunk) i))) (:buckets root2)))]
                (is (= 1 changed))
                (is (= #{105 200} (set (dti/search-eids (sec/-sec-restore (dti/make-index {:attrs [:decl/dt-key]} nil) store key-map2)
                                                        (dti/query-key (head-const 5)))))))))
          (finally (d/release conn)))))))
