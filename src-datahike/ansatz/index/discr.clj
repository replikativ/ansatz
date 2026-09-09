;; A CIC discrimination tree as a DURABLE datahike secondary index.
;;
;; The trie (`ansatz.tactic.discr-tree`: star-aware, Lean's getMatchLoop) keys every
;; declaration's CONCLUSION; a goal keyed the same way with its metavariables as `*`
;; matches every lemma that could unify, in microseconds, before any defeq is attempted.
;;
;; Today that trie is rebuilt in RAM at every boot (49.9 s for Mathlib's 348,654 keys).
;; Here it is a persistent structure over konserve: the trie is cut into size-bounded
;; CHUNKS, each a content-addressed konserve value (a subtree stored whole, or a node whose
;; children are `[:ref addr]`), loaded on first touch, path-copied on insert, flushed
;; bottom-up at commit. Restoring on `connect` is one root address; a query faults in only
;; the chunks it walks. Branching shares chunks by address (`-sec-branch` is O(1)); GC
;; marks by walking from the root.
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
           [java.util Collections LinkedHashMap Map]))

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
;; Persistent trie over konserve-addressed CHUNKS
;; ============================================================
;;
;; One konserve value per trie node is far too fine: Mathlib's 348,654 keys make millions
;; of nodes, i.e. millions of files and fsyncs on a filestore (the first 20k-key batch
;; wrote 45,617 files before this was chunked). Instead a node is persisted in one of two
;; forms, decided by the number of stored values beneath it (`:n`, maintained on insert):
;;
;;   small subtree (n ≤ chunk-max-values) → stored WHOLE: children inline, plain nested maps
;;   large node                            → stored with children as [:ref addr], each child
;;                                           flushed recursively by the same rule
;;
;; So the persisted trie is a tree of bounded-size chunks: connect loads the root chunk,
;; a query loads the one or two chunks it walks, a flush rewrites only the chunks on the
;; paths that changed (untouched children stay refs), and the in-memory matcher never
;; sees the difference because a loaded chunk's children are ordinary maps.

(def ^:private empty-node {:values [] :children {} :n 0})

(def chunk-max-values
  "A subtree with at most this many stored values is persisted whole as one chunk.
   Measured on Mathlib at 2,000: median chunk 2 KB, tens of thousands of chunks, and a
   broad query paid per-file overhead thousands of times (6 s cold). 20,000 keeps chunks in
   the tens-to-hundreds of KB, an order of magnitude fewer files, and wide nodes (the root,
   `Eq`) are the only multi-MB values — loaded once and cached."
  20000)

(defn- ref? [c] (and (vector? c) (= :ref (first c))))

(defn node-key
  "konserve key of a persisted chunk."
  [addr] [:ansatz.index/discr-node addr])

(def chunk-cache-size
  "Loaded chunks kept resident (LRU). A proving session walks a few hundred; a full
   import touches every chunk every commit, which is why the cache is also RESET at
   flush — superseded chunk versions must not stay resident (an unbounded map keyed by
   content address leaked every version of every chunk and blew a 4 GB heap at 180k keys)."
  4096)

(defn- new-cache ^Map []
  (Collections/synchronizedMap
   (proxy [LinkedHashMap] [256 (float 0.75) true]
     (removeEldestEntry [_] (> (.size ^Map this) chunk-cache-size)))))

(defn- load-chunk
  [store ^Map cache addr]
  (or (.get cache addr)
      (do (when (nil? store)
            (throw (ex-info "discr-tree: persisted chunk reached without a store" {:addr addr})))
          (let [n (k/get store (node-key addr) nil {:sync? true})]
            (when (nil? n)
              (throw (ex-info "discr-tree: persisted chunk missing" {:addr addr})))
            (.put cache addr n)
            n))))

(defn- resolve-child
  "A child is an in-memory node or a `[:ref addr]`; return the node."
  [{:keys [store cache]} c]
  (if (ref? c) (load-chunk store cache (second c)) c))

(defn- insert
  "Path-copying insert: nodes along the path become in-memory (dirty) nodes; untouched
   siblings stay as refs. `:n` counts stored values beneath a node."
  [ctx node keys eid]
  (let [node (update node :n (fnil inc 0))]
    (if (empty? keys)
      (update node :values (fnil conj []) eid)
      (let [k (first keys)
            child (resolve-child ctx (get (:children node) k empty-node))]
        (assoc-in node [:children k] (insert ctx child (rest keys) eid))))))

(defn- remove-eid
  "Path-copying removal; prunes nodes left with no values and no children."
  [ctx node keys eid]
  (if (empty? keys)
    (let [vs (vec (remove #(= (long %) (long eid)) (:values node)))]
      (-> node (assoc :values vs) (update :n (fnil #(max 0 (- % (- (count (:values node)) (count vs)))) 0))))
    (let [k (first keys)]
      (if-let [c (get (:children node) k)]
        (let [child (resolve-child ctx c)
              child' (remove-eid ctx child (rest keys) eid)
              removed (- (or (:n child) 0) (or (:n child') 0))
              node' (update node :n (fnil #(max 0 (- % removed)) 0))]
          (if (and (empty? (:values child')) (empty? (:children child')))
            (update node' :children dissoc k)
            (assoc-in node' [:children k] child')))
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
  "Lean's getMatchLoop over lazily loaded chunks: at each level explore the stored-star
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

(defn- inline-whole
  "A small subtree as a self-contained value: every ref beneath it loaded and inlined."
  [ctx node]
  (assoc node :children
         (reduce-kv (fn [m k c] (assoc m k (inline-whole ctx (resolve-child ctx c))))
                    {} (:children node))))

(defn- write-chunk! [store value]
  (let [addr (hasch/uuid value)]
    (k/assoc store (node-key addr) value {:sync? true})
    addr))

(defn- flush-node
  "Persist a node and return its content address. A subtree of at most chunk-max-values
   stored values is written WHOLE as one chunk; a larger node is written with its children
   as refs, each child flushed by the same rule. Children that are already refs are
   untouched (structural sharing across commits and branches)."
  [ctx node]
  (let [store (:store ctx)]
    (if (<= (or (:n node) 0) chunk-max-values)
      (write-chunk! store (inline-whole ctx node))
      (let [children' (reduce-kv (fn [m k c] (assoc m k (if (ref? c) c [:ref (flush-node ctx c)])))
                                 {} (:children node))]
        (write-chunk! store (assoc node :children children'))))))

(defn- all-addrs
  "Every persisted chunk address reachable from `child` (loads the whole trie — GC only)."
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

;; state: {:root node | [:ref addr], :store konserve | nil, :cache LRU Map addr → chunk}
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
          addr (flush-node ctx root)]
      ;; drop every resident chunk: superseded versions are garbage from here on and the
      ;; new root's chunks reload on demand
      (swap! state assoc :root [:ref addr] :store store :cache (new-cache))
      {:type :ansatz.index/discr-tree :branch branch :root addr :merkle-root addr}))
  (-sec-restore [_ store key-map]
    (->DiscrTreeIndex (atom {:root [:ref (:root key-map)] :store store :cache (new-cache)})
                      attrs))
  (-sec-branch [_ store _from-branch _new-branch]
    ;; nodes are content-addressed and immutable: the fork shares the root
    (->DiscrTreeIndex (atom (assoc @state :store store :cache (new-cache))) attrs))
  (-sec-mark [_]
    (let [st @state ctx (ctx-of st)]
      (set (map node-key (all-addrs ctx (:root st) #{})))))

  clojure.lang.IDeref
  (deref [_] @state))

(defmethod sec/mark-from-key-map :ansatz.index/discr-tree
  ;; GC's mark phase works from the stored key-map, without an index instance
  ;; (gc.cljc: `(sec/mark-from-key-map key-map store)`). The multimethod's default is #{},
  ;; which would let the sweep delete every live chunk of this index. Walk the chunk tree
  ;; from the root address through the store and return every chunk's konserve key.
  [key-map store]
  (if-let [root (:root key-map)]
    (set (map node-key (all-addrs {:store store :cache (new-cache)} [:ref root] #{})))
    #{}))

(defn make-index
  "Factory for register-index-type!: (config db) → an empty DiscrTreeIndex (a skeleton when
   `db` is nil; datahike then calls -sec-restore with the stored key-map)."
  [config _db]
  (->DiscrTreeIndex (atom {:root empty-node :store nil :cache (new-cache)})
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
