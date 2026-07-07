;; A CIC discrimination-tree as an EXTERNAL datahike secondary index.
;;
;; Validates that datahike's ISecondaryIndex framework is registerable from
;; outside (no datahike patch): we register a `:ansatz.index/discr-tree` type,
;; datahike feeds it the signed-delta datom stream for the watched attribute,
;; and its star-aware trie answers structural queries in ~µs (vs recursive
;; datalog). The stored value is each declaration's conclusion key-path
;; (`ansatz.tactic.discr-tree/expr->keys`, EDN-serialized as :decl/dt-key);
;; the index parses it on -transact.
(ns ansatz.index.discr
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [datahike.index.secondary :as sec]
            [datahike.index.entity-set :as es]
            [clojure.edn :as edn])
  (:import [ansatz.kernel Name]))

(defn- edn-safe-keys
  "Make a disc-tree key-path EDN-round-trippable: the `:name` of a :const key is
   a kernel Name object → stringify it. Applied to BOTH stored and query keys so
   they compare consistently in the trie."
  [keys]
  (mapv (fn [k]
          (if (instance? Name (:name k))
            (update k :name nm/->string)
            k))
        keys))

(defn- eids->bitset
  "Build an EntityBitSet from eids, intersecting an optional entity-filter."
  [eids entity-filter]
  (let [bs (es/entity-bitset)]
    (doseq [eid eids
            :when (or (nil? entity-filter)
                      (es/entity-bitset-contains? entity-filter (long eid)))]
      (es/entity-bitset-add! bs (long eid)))
    bs))

(defn- matching-eids
  "trie-match for a query-spec. `:query` is either a key-path vector (from
   dt/expr->keys) or its EDN string; star keys match any subterm."
  [trie query-spec]
  (let [q (:query query-spec)
        keys (cond (string? q) (edn/read-string q)
                   (vector? q) q
                   :else [])]
    (distinct (dt/trie-match trie keys))))

;; state = {:trie <disc-tree>, :attrs #{watched attrs}}
(defrecord DiscrTreeIndex [state attrs]
  sec/ISecondaryIndex
  (-search [_ query-spec entity-filter]
    (eids->bitset (matching-eids (:trie @state) query-spec) entity-filter))
  (-estimate [_ query-spec]
    (count (matching-eids (:trie @state) query-spec)))
  (-can-order? [_ _ _] false)
  (-slice-ordered [_ _ _ _ _ _] nil)
  (-indexed-attrs [_] attrs)
  (-transact [this {:keys [datom added?]}]
    ;; datom = [e a v tx]; v = EDN key-path string. Insert on assert.
    ;; (Retraction/rebuild deferred — declarations are effectively append-only.)
    (when added?
      (let [eid (long (nth datom 0))
            keys (edn/read-string (nth datom 2))]
        (swap! state update :trie dt/trie-insert keys eid)))
    this)

  clojure.lang.IDeref
  (deref [_] @state))

(defn make-index
  "Factory for register-index-type!: (config db) → a fresh DiscrTreeIndex."
  [config _db]
  (->DiscrTreeIndex (atom {:trie dt/empty-trie})
                    (set (:attrs config))))

(defonce register!
  (sec/register-index-type! :ansatz.index/discr-tree make-index))

;; ---- helpers for producing the stored key + a query key-path ----

(defn conclusion-key
  "The EDN-serialized discrimination key-path of an expression (for storage as
   :decl/dt-key). `expr` should be the declaration's CONCLUSION."
  [expr]
  (pr-str (edn-safe-keys (dt/expr->keys expr))))

(defn decl-key
  "Stored disc-tree key for a declaration TYPE: peel the ∀-telescope,
   substituting metavariables for the bound variables so they key as STAR
   wildcards, then key the conclusion. A lemma `∀ n, 0 ≤ n` is thus stored as
   `0 ≤ *` and structurally matches any `0 ≤ k` query (the kernel `defeq`
   confirmation then decides which candidates truly apply)."
  [ty]
  (loop [t ty, i 0]
    (if (e/forall? t)
      (recur (e/instantiate1 (e/forall-body t) (e/mvar (+ 800000 i))) (inc i))
      (conclusion-key t))))

(defn query-key
  "A query key-path (vector) from a pattern expression; holes/mvars become
   star wildcards inside dt/expr->keys."
  [expr]
  (edn-safe-keys (dt/expr->keys expr)))

;; ---- datalog foreign var: query the disc-tree index from a datalog clause ----
;; Direction-2 seam. In a query:
;;   [(ansatz.index.discr/dt-match :idx/dt ?goal-key) [[?d]]]
;; routes (via :filter mode) to the schema-declared :idx/dt secondary index,
;; binding ?d to each declaration entity whose conclusion structurally matches
;; ?goal-key (µs, star-aware). The var body is unused — the executor calls the
;; index's -search directly; it only needs to resolve to a truthy var carrying
;; the metadata.
(defn ^{:datahike/external-engine
        {:index-key 0                        ; arg 0 = the index ident
         :binding-columns [:entity-id]       ; → :filter mode (entity-id out)
         :input-vars :all-bound              ; the query key must be bound
         :cost-model (fn [_db _idx _args _n] {:estimated-card 30})}}
  dt-match
  [_idx-ident _goal-key] true)
