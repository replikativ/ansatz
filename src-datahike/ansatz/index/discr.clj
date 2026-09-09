;; A CIC discrimination tree as a DURABLE datahike secondary index.
;;
;; The trie (`ansatz.tactic.discr-tree`: star-aware, Lean's getMatchLoop) keys every
;; declaration's CONCLUSION; a goal keyed the same way with its metavariables as `*`
;; matches every lemma that could unify, in microseconds, before any defeq is attempted.
;;
;; Today that trie is rebuilt in RAM at every boot (49.9 s for Mathlib's 348,654 keys).
;; Here it is a persistent structure over konserve: each trie node is a content-addressed
;; konserve value `{:values [eid …] :children {key → [:ref addr] | node}}`, loaded on first
;; touch, path-copied on insert, flushed bottom-up at commit. Restoring on `connect` is one
;; root address; the first query faults in only the nodes it walks. Branching shares nodes
;; by address (`-sec-branch` is O(1)); GC marks by walking from the root.
;;
;; datahike wiring (no datahike patch): registered through the public
;; `register-index-type!`, declared in the schema as
;;   {:db/ident :idx/dt :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/dt-key]}
;; and fed the signed-delta datom stream for the watched attribute. The stored value is
;; the EDN key-path (`conclusion-key` / `decl-key`); queries pass a key-path or its EDN.
(ns ansatz.index.discr
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [datahike.index.secondary :as sec]
            [datahike.index.entity-set :as es]
            [konserve.core :as k]
            [hasch.core :as hasch]
            [clojure.edn :as edn])
  (:import [ansatz.kernel Name]
           [java.util.concurrent ConcurrentHashMap]))

;; ============================================================
;; Keys
;; ============================================================

(def ^:private star-key {:tag :star})

(defn- edn-safe-keys
  "Make a disc-tree key-path EDN-round-trippable: the `:name` of a :const key is a kernel
   Name object → stringify it. Applied to BOTH stored and query keys so they compare
   consistently in the trie."
  [keys]
  (mapv (fn [k]
          (if (instance? Name (:name k))
            (update k :name nm/->string)
            k))
        keys))

(defn conclusion-key
  "The EDN-serialized discrimination key-path of an expression (for storage as
   :decl/dt-key). `expr` should be the declaration's CONCLUSION."
  [expr]
  (pr-str (edn-safe-keys (dt/expr->keys expr))))

(defn decl-key
  "Stored disc-tree key for a declaration TYPE: peel the ∀-telescope, substituting
   metavariables for the bound variables so they key as STAR wildcards, then key the
   conclusion. A lemma `∀ n, 0 ≤ n` is thus stored as `0 ≤ *` and structurally matches any
   `0 ≤ k` query (the kernel `defeq` confirmation then decides which candidates apply)."
  [ty]
  (loop [t ty, i 0]
    (if (e/forall? t)
      (recur (e/instantiate1 (e/forall-body t) (e/mvar (+ 800000 i))) (inc i))
      (conclusion-key t))))

(defn query-key
  "A query key-path (vector) from a pattern expression; holes/mvars become star
   wildcards inside dt/expr->keys."
  [expr]
  (edn-safe-keys (dt/expr->keys expr)))

(defn- query-keys [query-spec]
  (let [q (:query query-spec)]
    (cond (string? q) (edn/read-string q)
          (vector? q) q
          :else [])))

;; ============================================================
;; Persistent trie over konserve-addressed nodes
;; ============================================================

(def ^:private empty-node {:values [] :children {}})

(defn- ref? [c] (and (vector? c) (= :ref (first c))))

(defn node-key
  "konserve key of a persisted trie node."
  [addr] [:ansatz.index/discr-node addr])

(defn- load-node
  [store ^ConcurrentHashMap cache addr]
  (or (.get cache addr)
      (do (when (nil? store)
            (throw (ex-info "discr-tree: persisted node reached without a store" {:addr addr})))
          (let [n (k/get store (node-key addr) nil {:sync? true})]
            (when (nil? n)
              (throw (ex-info "discr-tree: persisted node missing" {:addr addr})))
            (.put cache addr n)
            n))))

(defn- resolve-child
  "A child is an in-memory node or a `[:ref addr]`; return the node."
  [{:keys [store cache]} c]
  (if (ref? c) (load-node store cache (second c)) c))

(defn- insert
  "Path-copying insert: nodes along the path become in-memory (dirty) nodes; untouched
   siblings stay as refs."
  [ctx node keys eid]
  (if (empty? keys)
    (update node :values (fnil conj []) eid)
    (let [k (first keys)
          child (resolve-child ctx (get (:children node) k empty-node))]
      (assoc-in node [:children k] (insert ctx child (rest keys) eid)))))

(defn- remove-eid
  "Path-copying removal; prunes nodes left with no values and no children."
  [ctx node keys eid]
  (if (empty? keys)
    (update node :values (fn [vs] (vec (remove #(= (long %) (long eid)) vs))))
    (let [k (first keys)]
      (if-let [c (get (:children node) k)]
        (let [child' (remove-eid ctx (resolve-child ctx c) (rest keys) eid)]
          (if (and (empty? (:values child')) (empty? (:children child')))
            (update node :children dissoc k)
            (assoc-in node [:children k] child')))
        node))))

(defn- skip-subtree
  "Skip one full argument (1 key + its arity sub-args, recursively) — what a stored `*`
   consumes of the query. Same as ansatz.tactic.discr-tree."
  [ks]
  (if (empty? ks)
    ks
    (let [k (first ks) arity (or (:arity k) 0)]
      (loop [r (rest ks) n arity]
        (if (zero? n) r (recur (skip-subtree r) (dec n)))))))

(defn- match
  "Lean's getMatchLoop over lazily loaded nodes: at each level explore the stored-star
   branch (skipping a full subterm of the query), the exact key, and — when the query key is
   itself a star — every child."
  [ctx node keys]
  (if (empty? keys)
    (:values node [])
    (let [k (first keys)
          rest-keys (rest keys)
          children (:children node {})
          star-results (when-let [c (get children star-key)]
                         (match ctx (resolve-child ctx c) (skip-subtree keys)))
          exact-results (when (not= k star-key)
                          (when-let [c (get children k)]
                            (match ctx (resolve-child ctx c) rest-keys)))
          all-results (when (= k star-key)
                        (mapcat (fn [[ck c]]
                                  (when (not= ck star-key)
                                    (match ctx (resolve-child ctx c) rest-keys)))
                                children))]
      (into [] (concat star-results exact-results all-results)))))

(defn- flush-node
  "Persist a node and its dirty descendants; return the node's content address. Children
   that are already refs are untouched (structural sharing across commits and branches)."
  [store node]
  (let [children' (reduce-kv (fn [m k c] (assoc m k (if (ref? c) c [:ref (flush-node store c)])))
                             {} (:children node))
        persisted {:values (vec (:values node)) :children children'}
        addr (hasch/uuid persisted)]
    (k/assoc store (node-key addr) persisted {:sync? true})
    addr))

(defn- all-addrs
  "Every persisted node address reachable from `child` (loads the whole trie — GC only)."
  [ctx child acc]
  (if (ref? child)
    (let [addr (second child)]
      (if (contains? acc addr)
        acc
        (reduce (fn [a c] (all-addrs ctx c a))
                (conj acc addr)
                (vals (:children (resolve-child ctx child))))))
    (reduce (fn [a c] (all-addrs ctx c a)) acc (vals (:children child)))))

(defn- eids->bitset
  [eids entity-filter]
  (let [bs (es/entity-bitset)]
    (doseq [eid eids
            :when (or (nil? entity-filter)
                      (es/entity-bitset-contains? entity-filter (long eid)))]
      (es/entity-bitset-add! bs (long eid)))
    bs))

(defn- ctx-of [st] {:store (:store st) :cache (:cache st)})

;; ============================================================
;; The index
;; ============================================================

;; state: {:root node | [:ref addr], :store konserve | nil, :cache ConcurrentHashMap addr → node}
(defrecord DiscrTreeIndex [state attrs]
  sec/ISecondaryIndex
  (-search [_ query-spec entity-filter]
    (let [st @state ctx (ctx-of st)]
      (eids->bitset (distinct (match ctx (resolve-child ctx (:root st)) (query-keys query-spec)))
                    entity-filter)))
  (-estimate [_ query-spec]
    (let [st @state ctx (ctx-of st)]
      (count (distinct (match ctx (resolve-child ctx (:root st)) (query-keys query-spec))))))
  (-can-order? [_ _ _] false)
  (-slice-ordered [_ _ _ _ _ _] nil)
  (-indexed-attrs [_] attrs)
  (-transact [this {:keys [datom added?]}]
    ;; datom = [e a v tx]; v = EDN key-path string.
    (let [eid (long (nth datom 0))
          keys (edn/read-string (nth datom 2))]
      (swap! state (fn [st]
                     (let [ctx (ctx-of st)
                           root (resolve-child ctx (:root st))]
                       (assoc st :root (if added?
                                         (insert ctx root keys eid)
                                         (remove-eid ctx root keys eid)))))))
    this)

  sec/IVersionedSecondaryIndex
  (-sec-flush [_ store branch]
    (let [st @state
          ctx (assoc (ctx-of st) :store store)
          root (resolve-child ctx (:root st))
          addr (flush-node store root)]
      (swap! state assoc :root [:ref addr] :store store)
      {:type :ansatz.index/discr-tree :branch branch :root addr :merkle-root addr}))
  (-sec-restore [_ store key-map]
    (->DiscrTreeIndex (atom {:root [:ref (:root key-map)] :store store :cache (ConcurrentHashMap.)})
                      attrs))
  (-sec-branch [_ store _from-branch _new-branch]
    ;; nodes are content-addressed and immutable: the fork shares the root
    (->DiscrTreeIndex (atom (assoc @state :store store :cache (ConcurrentHashMap.))) attrs))
  (-sec-mark [_]
    (let [st @state ctx (ctx-of st)]
      (set (map node-key (all-addrs ctx (:root st) #{})))))

  clojure.lang.IDeref
  (deref [_] @state))

(defn make-index
  "Factory for register-index-type!: (config db) → an empty DiscrTreeIndex (a skeleton when
   `db` is nil; datahike then calls -sec-restore with the stored key-map)."
  [config _db]
  (->DiscrTreeIndex (atom {:root empty-node :store nil :cache (ConcurrentHashMap.)})
                    (set (:attrs config))))

(defonce register!
  (sec/register-index-type! :ansatz.index/discr-tree make-index))

(defn search-eids
  "Direct query: the matching entity ids for a key-path (vector or EDN string) — the
   recall provider's entry point, bypassing the datalog planner."
  [index key-path]
  (let [st @(:state index) ctx (ctx-of st)]
    (distinct (match ctx (resolve-child ctx (:root st))
                     (if (string? key-path) (edn/read-string key-path) key-path)))))

;; ---- datalog foreign var: query the disc-tree index from a datalog clause ----
;; In a query:
;;   [(ansatz.index.discr/dt-match :idx/dt ?goal-key) [[?d]]]
;; routes (via :filter mode) to the schema-declared :idx/dt secondary index, binding ?d to
;; each declaration entity whose conclusion structurally matches ?goal-key. The var body is
;; unused — the executor calls the index's -search directly.
(defn ^{:datahike/external-engine
        {:index-key 0
         :binding-columns [:entity-id]
         :input-vars :all-bound
         :cost-model (fn [_db _idx _args _n] {:estimated-card 30})}}
  dt-match
  [_idx-ident _goal-key] true)
