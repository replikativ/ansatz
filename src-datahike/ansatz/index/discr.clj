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

(def ^:dynamic chunk-max-values
  "A subtree with at most this many stored values is persisted whole as one chunk.
   Dynamic so tests can force the large-node/bucket paths on small data."
  20000)

(defn- ref? [c] (and (vector? c) (= :ref (first c))))
(defn- bref? [c] (and (vector? c) (= :bref (first c))))

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

;; ---- children: node | [:ref addr] | [:bref i] ------------------------------------------
;;
;; A persisted LARGE node keeps its small children in K sibling BUCKET chunks, assigned by
;; key hash: the node's own chunk holds `k → [:bref i]` plus `:buckets {i → addr}` and
;; `:nb K`; a bucket chunk is `{k → inline subtree}`. A lookup loads the node and ONE
;; bucket; a flush rewrites only the buckets whose children changed. (Inlining small
;; children into the parent instead made an 18 MB root on Mathlib, and reffing each one
;; separately made 21k files — buckets bound both.)

(defn- child-of
  "Resolve the child at key `k` of an in-memory or loaded `node`, or nil."
  [{:keys [store cache]} node k]
  (let [c (get (:children node) k)]
    (cond (nil? c) nil
          (ref? c) (load-chunk store cache (second c))
          (bref? c) (let [addr (get-in node [:buckets (second c)])]
                      (when addr (get (load-chunk store cache addr) k)))
          :else c)))

(defn- resolve-child
  "A child value that is a `[:ref addr]`; return the node (used for the root)."
  [{:keys [store cache]} c]
  (if (ref? c) (load-chunk store cache (second c)) c))

(defn- mark-dirty-bucket [node c]
  (if (bref? c) (update node :dirty-buckets (fnil conj #{}) (second c)) node))

(defn- insert
  "Path-copying insert: nodes along the path become in-memory (dirty) nodes; untouched
   siblings stay as refs / in their buckets. `:n` counts stored values beneath a node."
  [ctx node keys eid]
  (let [node (update node :n (fnil inc 0))]
    (if (empty? keys)
      (update node :values (fnil conj []) eid)
      (let [k (first keys)
            c (get (:children node) k)
            child (or (child-of ctx node k) empty-node)]
        (-> (mark-dirty-bucket node c)
            (assoc-in [:children k] (insert ctx child (rest keys) eid)))))))

(defn- remove-eid
  "Path-copying removal; prunes nodes left with no values and no children."
  [ctx node keys eid]
  (if (empty? keys)
    (let [vs (vec (remove #(= (long %) (long eid)) (:values node)))
          removed (- (count (:values node)) (count vs))]
      (-> node (assoc :values vs) (update :n (fnil #(max 0 (- % removed)) 0))))
    (let [k (first keys)
          c (get (:children node) k)]
      (if-let [child (child-of ctx node k)]
        (let [child' (remove-eid ctx child (rest keys) eid)
              removed (- (or (:n child) 0) (or (:n child') 0))
              node' (-> (mark-dirty-bucket node c)
                        (update :n (fnil #(max 0 (- % removed)) 0)))]
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
  [ctx node ks]
  (if (empty? ks)
    (:values node [])
    (let [k (first ks)
          rest-keys (rest ks)
          children (:children node {})
          star-results (when (contains? children star-key)
                         (match ctx (child-of ctx node star-key) (skip-subtree ks)))
          exact-results (when (and (not= k star-key) (contains? children k))
                          (match ctx (child-of ctx node k) rest-keys))
          all-results (when (= k star-key)
                        (mapcat (fn [ck]
                                  (when (not= ck star-key)
                                    (match ctx (child-of ctx node ck) rest-keys)))
                                (clojure.core/keys children)))]
      (into [] (concat star-results exact-results all-results)))))

(defn- inline-whole
  "A small subtree as a self-contained value: every ref/bucket beneath it resolved and
   inlined; bucket bookkeeping dropped."
  [ctx node]
  {:values (vec (:values node))
   :n (or (:n node) 0)
   :children (reduce (fn [m k] (assoc m k (inline-whole ctx (child-of ctx node k))))
                     {} (keys (:children node)))})

(defn- write-chunk! [store value]
  (let [addr (hasch/uuid value)]
    (k/assoc store (node-key addr) value {:sync? true})
    addr))

(defn- bucket-of [k nb] (mod (Math/abs (long (hash k))) nb))

(defn- flush-node
  "Persist a node and return its content address.

   A subtree of at most chunk-max-values stored values is written WHOLE as one chunk. A
   larger node: children that are themselves large (in memory and > cap, or already
   [:ref …]) are written as refs; small children go to K sibling buckets by key hash —
   only buckets holding a changed child are rewritten (old contents merged), the rest keep
   their address. The node's own chunk holds the refs, `k → [:bref i]`, `:buckets` and
   `:nb`. K is fixed at the node's first large flush (`:nb`)."
  [ctx node]
  (let [store (:store ctx)
        n (or (:n node) 0)]
    (if (<= n chunk-max-values)
      (write-chunk! store (inline-whole ctx node))
      (let [children (:children node)
            in-mem (into {} (filter (fn [[_ c]] (and (map? c))) children))
            small-mem (into {} (filter (fn [[_ c]] (<= (or (:n c) 0) chunk-max-values)) in-mem))
            big-mem (apply dissoc in-mem (keys small-mem))
            nb (or (:nb node)
                   (max 1 (int (Math/ceil (/ (double (reduce + (map :n (vals small-mem))))
                                             (double chunk-max-values))))))
            old-buckets (or (:buckets node) {})
            ;; buckets to rewrite: those of changed small children + those flagged by
            ;; modification/removal of a formerly bucketed child
            dirty (into (or (:dirty-buckets node) #{})
                        (map #(bucket-of % nb) (keys small-mem)))
            live-keys (set (keys children))
            buckets' (reduce (fn [bs i]
                               (let [base (if-let [a (get old-buckets i)]
                                            (load-chunk store (:cache ctx) a) {})
                                     ;; drop entries whose key left this node or became big/in-memory
                                     base (into {} (filter (fn [[k _]] (and (contains? live-keys k)
                                                                             (bref? (get children k))))
                                                           base))
                                     mine (into {} (filter (fn [[k _]] (= i (bucket-of k nb))) small-mem))
                                     merged (reduce-kv (fn [m k c] (assoc m k (inline-whole ctx c))) base mine)]
                                 (if (empty? merged)
                                   (dissoc bs i)
                                   (assoc bs i (write-chunk! store merged)))))
                             old-buckets dirty)
            children' (reduce-kv (fn [m k c]
                                   (assoc m k (cond (contains? small-mem k) [:bref (bucket-of k nb)]
                                                    (contains? big-mem k)   [:ref (flush-node ctx c)]
                                                    :else c)))   ; [:ref …] or [:bref …] unchanged
                                 {} children)]
        (write-chunk! store {:values (vec (:values node)) :n n :children children'
                             :buckets buckets' :nb nb})))))

(defn- all-addrs
  "Every persisted chunk address reachable from a resolved node (GC only)."
  [ctx node acc]
  (let [acc (into acc (vals (:buckets node)))]
    (reduce-kv (fn [a _ c]
                 (if (ref? c)
                   (let [addr (second c)]
                     (if (contains? a addr) a (all-addrs ctx (resolve-child ctx c) (conj a addr))))
                   (if (map? c) (all-addrs ctx c a) a)))
               acc (:children node))))

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
    (let [st @state ctx (ctx-of st) root (:root st)]
      (set (map node-key (all-addrs ctx (resolve-child ctx root)
                                    (if (ref? root) #{(second root)} #{}))))))

  clojure.lang.IDeref
  (deref [_] @state))

(defmethod sec/mark-from-key-map :ansatz.index/discr-tree
  ;; GC's mark phase works from the stored key-map, without an index instance
  ;; (gc.cljc: `(sec/mark-from-key-map key-map store)`). The multimethod's default is #{},
  ;; which would let the sweep delete every live chunk of this index. Walk the chunk tree
  ;; from the root address through the store and return every chunk's konserve key.
  [key-map store]
  (if-let [root (:root key-map)]
    (let [ctx {:store store :cache (new-cache)}]
      (set (map node-key (all-addrs ctx (resolve-child ctx [:ref root]) #{root}))))
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
