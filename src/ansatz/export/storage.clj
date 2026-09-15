;; PSS-backed persistent store for Ansatz kernel.
(ns ansatz.export.storage
  "Durable persistence for Ansatz kernel state using PSS + konserve.
   Four PSS indices store names, levels, expressions, and environment
   declarations. Branching (forking) copies only root addresses — O(1)
   with full structural sharing.

   Storage stack: PSS → CachedStorage (IStorage) → konserve filestore at `<store>/blobs`.

   STORE FORMAT 1 (see ansatz.store/store-format): every PSS node is one CBOR blob
   (ansatz.export.codec) written as BINARY under a CONTENT ADDRESS — the SHA-256 of its
   bytes as a UUID — so an identical node has one address everywhere: two imports of the
   same library produce the same roots, an unchanged subtree costs nothing across library
   versions, and a store can be mirrored or served remotely by address. Non-node values
   (branch metadata, decl-order chunks, derived state) go through konserve's boring
   serializer over the same tag registry. There is no Fressian and no legacy reader: a
   store of another format is refused at open, and the answer is to re-import
   (ansatz.import), not to migrate."
  (:require [konserve.core :as k]
            [ansatz.export.codec :as codec]
            [boring.core :as boring]
            [konserve.filestore :as fs]
            [konserve.serializers :as ser]
            [clojure.java.io :as io]
            [clojure.edn :as edn]
            [org.replikativ.persistent-sorted-set :as pss]
            [ansatz.kernel.name :as ansatz-name]
            [ansatz.export.parser :as parser]
            [ansatz.export.types])
  (:import [ansatz.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule Env ExprStore TypeChecker InductiveBundle]
           [ansatz.export.types CIShell]
           [org.replikativ.persistent_sorted_set PersistentSortedSet IStorage Leaf Branch Settings RefType]
           [java.security MessageDigest]
           [java.util UUID List ArrayList]))

;; ============================================================
;; Comparators for PSS indices
;; ============================================================

(def id-cmp
  "Comparator for [int-id, value] entries — compare by first element."
  (fn [a b]
    (compare (long (nth a 0)) (long (nth b 0)))))

(def name-cmp
  "Comparator for [Name, ConstantInfo] entries — compare by Name.toString for stable ordering."
  (fn [a b]
    (compare (.toString ^Name (nth a 0))
             (.toString ^Name (nth b 0)))))

(defn- long-prop
  [prop-name default]
  (try
    (let [v (Long/parseLong (System/getProperty prop-name (str default)))]
      (if (pos? v) v default))
    (catch Throwable _
      default)))

;; ============================================================
;; CachedStorage (IStorage implementation)
;; ============================================================

(defn content-address
  "The address of a node blob: its SHA-256, folded to a UUID. Deterministic in the bytes, so
   identical nodes coincide and a store's roots are a function of its content."
  ^UUID [^bytes bs]
  (let [d (.digest (MessageDigest/getInstance "SHA-256") bs)
        bb (java.nio.ByteBuffer/wrap d)]
    (UUID. (.getLong bb) (.getLong bb))))

(defn- read-blob ^bytes [store address]
  (k/bget store address
          (fn [{:keys [input-stream]}] (.readAllBytes ^java.io.InputStream input-stream))
          {:sync? true}))

;; PSS calls `store` bottom-up — a Branch stores its dirty children first, then itself — so a
;; node's child addresses are settled when it is encoded here, and its own address can be its
;; content hash. Nodes are ENCODED ONCE: the bytes are hashed for the address and kept as the
;; pending write (flush-writes! puts them as binary blobs, bypassing konserve's serializer).
;; No address reuse and no freelist: with content addresses an address is owned by its
;; bytes, never by a tree, so a node "freed" by one tree may still be another's.
(deftype CachedStorage [store registry pending-writes settings-atom]
  IStorage
  (store [_ node]
    (let [^bytes bs (boring/encode node {:registry registry})
          address (content-address bs)]
      (swap! pending-writes conj [address bs])
      address))

  (restore [_ address]
    (let [bs (read-blob store address)]
      (when (nil? bs)
        (throw (ex-info "Node not found in storage" {:address address})))
      (boring/decode bs {:registry registry})))

  (accessed [_ _address] nil)
  (markFreed [_ _address] nil)
  (isFreed [_ _address] false))

(defn flush-writes!
  "Write every pending node blob to konserve (binary, already encoded), in parallel batches."
  [storage]
  (let [^CachedStorage cs storage
        writes @(.pending-writes cs)
        kstore (.store cs)]
    (reset! (.pending-writes cs) [])
    (when (seq writes)
      (doseq [batch (partition-all 64 writes)]
        (let [futures (mapv (fn [[addr ^bytes bs]]
                              (future (k/bassoc kstore addr bs {:sync? true})))
                            batch)]
          (doseq [f futures] @f))))))

;; ============================================================
;; Store lifecycle
;; ============================================================

(defn blobs-dir
  "The konserve directory of the store at `store-path`: `<store>/blobs`. Nothing but blobs
   lives there — konserve treats every file in its directory as a blob (its `keys` and GC
   walk them), so the manifest, catalogue and inputs are siblings, never children."
  ^java.io.File [store-path] (io/file store-path "blobs"))

(defn open-store
  "Open the store rooted at `store-path` (creating `<store>/blobs` if absent). Returns
   {:store konserve, :storage CachedStorage, :settings-atom, :path}.

   Opening does NOT check the manifest — `ansatz.store/check-format!` does, and `init!` calls
   it; the importer opens a store that has no manifest yet.

   `:sync-blob?` (default true) fsyncs each blob write. An import turns it off: a crashed
   import is simply re-run, and the manifest is written last."
  ([store-path] (open-store store-path {}))
  ([store-path {:keys [sync-blob?] :or {sync-blob? true}}]
   (let [dir (blobs-dir store-path)
         _ (.mkdirs dir)
         settings-atom (atom (Settings. 64 RefType/WEAK))
         storage-atom (atom nil)
         ;; the PSS root handler resolves its storage through a write-once cell, as the
         ;; storage does not exist until the store is open
         registry (codec/registry (fn [_] @storage-atom))
         kstore (fs/connect-fs-store
                 (.getPath dir)
                 :opts {:sync? true}
                 :config {:sync-blob? sync-blob?
                          :encoding {:serializer :BoringSerializer
                                     :serializers {:BoringSerializer (ser/boring-serializer registry)}}})
         cached (->CachedStorage kstore registry (atom []) settings-atom)]
     (reset! storage-atom cached)
     {:store kstore
      :storage cached
      :settings-atom settings-atom
      :path store-path})))

(defn close-store
  "Close the store, flushing pending writes."
  [store-map]
  (flush-writes! (:storage store-map)))

;; ============================================================
;; Persist — build PSS indices from parsed data
;; ============================================================

(defn- build-pss-from-entries
  "Build a PSS from a sorted vector of entries using the given comparator and storage."
  [entries cmp ^CachedStorage storage & {:keys [branching-factor] :or {branching-factor 64}}]
  (let [arr (object-array entries)]
    (pss/from-sorted-array cmp arr (alength arr)
                           {:storage storage
                            :branching-factor branching-factor
                            :ref-type :weak})))

(defn- persist-pss!
  "Build a PSS from entries, store it, flush writes, return [root count]."
  [entries cmp ^CachedStorage storage label & {:keys [branching-factor] :or {branching-factor 64}}]
  (let [t0 (System/currentTimeMillis)
        pss (build-pss-from-entries entries cmp storage :branching-factor branching-factor)
        root (pss/store pss)
        pending (count @(.pending-writes storage))]
    (println "  PSS built:" (- (System/currentTimeMillis) t0) "ms," pending "pending writes")
    (flush-writes! storage)
    (println " " label "done:" (- (System/currentTimeMillis) t0) "ms, root:" root)
    [root (count entries)]))

(defn- log!
  "Append a log line to the given log file and also println."
  [^java.io.Writer log-writer & args]
  (let [msg (apply str (interpose " " args))]
    (println msg)
    (.write log-writer msg)
    (.write log-writer "\n")
    (.flush log-writer)))

(defn- persist-pss-streaming!
  "Build PSS incrementally by conjing entries from a sequential source.
   Avoids materializing all entries in memory — only the current rightmost path
   and pending writes are kept. Periodically calls pss/store + flush to allow
   weak refs to release stored nodes.

   reader-fn: (fn [i] entry-or-nil) for i in [0, max-id)
   Returns [root count]."
  [max-id reader-fn cmp ^CachedStorage storage label log-writer
   & {:keys [branching-factor flush-interval]
      :or {branching-factor 512 flush-interval 100000}}]
  (let [t0 (System/currentTimeMillis)
        empty-pss (pss/sorted-set* {:cmp cmp
                                    :storage storage
                                    :branching-factor branching-factor
                                    :ref-type :weak})
        cnt (atom 0)]
    (loop [pss empty-pss
           i 0]
      (if (< i max-id)
        (let [entry (reader-fn i)
              pss' (if entry
                     (do (swap! cnt inc)
                         (clojure.core/conj pss entry))
                     pss)]
          (when (and (pos? i) (zero? (mod i flush-interval)))
            ;; Store all in-memory nodes so weak refs can release them
            (pss/store pss')
            (flush-writes! storage)
            (System/gc)
            (when log-writer
              (let [rt (Runtime/getRuntime)
                    used (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                (log! log-writer (str "    " label " " i "/" max-id
                                      " entries=" @cnt " mem=" used "MB"
                                      " " (- (System/currentTimeMillis) t0) "ms")))))
          (recur pss' (inc i)))
        (let [root (pss/store pss)]
          (flush-writes! storage)
          (log! log-writer (str "  " label " done: " @cnt " entries in "
                                (- (System/currentTimeMillis) t0) "ms, root: " root))
          [root @cnt])))))

(defn persist-all!
  "Persist parsed state to the store.

   parser-state: result of parser/parse-ndjson-file (with :names, :levels, :exprs, :decls, :meta)
   env: an Env built from the declarations
   branch-name: string name for this branch (e.g. \"main\")"
  [store-map parser-state env branch-name]
  (let [{:keys [storage]} store-map
        ^ArrayList names-al (:names parser-state)
        ^ArrayList levels-al (:levels parser-state)
        ^ExprStore expr-store (:exprs parser-state)
        decls (:decls parser-state)]

    ;; Each PSS is built in its own scope so entries can be GC'd
    ;; 1. Names PSS: [id, Name]
    (println "Building names PSS..." (.size names-al) "entries")
    (let [[names-root names-count]
          (persist-pss! (into []
                              (for [i (range (.size names-al))
                                    :let [n (.get names-al i)]
                                    :when (some? n)]
                                [(long i) n]))
                        id-cmp storage "names")

          ;; 2. Levels PSS: [id, Level]
          _ (println "Building levels PSS..." (.size levels-al) "entries")
          [levels-root levels-count]
          (persist-pss! (into []
                              (for [i (range (.size levels-al))
                                    :let [l (.get levels-al i)]
                                    :when (some? l)]
                                [(long i) l]))
                        id-cmp storage "levels")

          ;; 3. Exprs PSS: [id, byte[]] — built and persisted, then released
          _ (println "Building exprs PSS..." (.maxId expr-store) "entries")
          [exprs-root exprs-count]
          (let [t2 (System/currentTimeMillis)
                entries (into []
                              (for [i (range (.maxId expr-store))]
                                (try
                                  [(long i) (.readRaw expr-store (int i))]
                                  (catch Exception _ nil))))
                entries (filterv some? entries)]
            (println "  entries built:" (- (System/currentTimeMillis) t2) "ms")
            (persist-pss! entries id-cmp storage "exprs"))]

      ;; 4. Env PSS: [Name, ConstantInfo]
      ;; exprs-entries is now out of scope and eligible for GC
      (System/gc)
      (println "Building env PSS..." (count decls) "entries")
      (let [[env-root env-count]
            (persist-pss! (->> decls
                               (mapv (fn [^ConstantInfo ci] [(.name ci) ci]))
                               (sort-by (fn [[^Name n _]] (.toString n)))
                               vec)
                          name-cmp storage "env")

            branch-meta {:names-root names-root
                         :names-count names-count
                         :levels-root levels-root
                         :levels-count levels-count
                         :exprs-root exprs-root
                         :exprs-count exprs-count
                         :env-root env-root
                         :env-count env-count
                         :quot-enabled (.isQuotEnabled ^Env env)
                         :timestamp (System/currentTimeMillis)
                         :meta (:meta parser-state)}]

        (k/assoc (:store store-map)
                 [:branches branch-name]
                 branch-meta
                 {:sync? true})
        (println "Branch" (pr-str branch-name) "persisted.")
        branch-meta))))

;; ============================================================
;; Store backend abstraction (LMDB or filestore)
;; ============================================================

(defn store-put
  "Put a single key-value pair to the konserve filestore."
  [store k v]
  (k/assoc store k v {:sync? true}))

(defn store-get
  "Get a value from the konserve filestore."
  [store k]
  (k/get store k nil {:sync? true}))

(defn derived-key
  "konserve key of a piece of DERIVED state for a branch — attrs, instances, matchers, recall
   keys, simp keys, the simp trie: everything `init!` used to re-derive from sidecar files at
   every start, computed once by the importer."
  [branch-name k] [:derived branch-name k])

(defn write-derived! [store branch-name k v] (k/assoc store (derived-key branch-name k) v {:sync? true}))
(defn read-derived [store branch-name k] (k/get store (derived-key branch-name k) nil {:sync? true}))

(defn store-multi-put
  "Batch put key-value pairs to the konserve filestore."
  [store entries]
  (let [batch-size 64]
    (doseq [batch (partition-all batch-size entries)]
      (let [futures (mapv (fn [[k v]]
                            (future (k/assoc store k v {:sync? true})))
                          batch)]
        (doseq [f futures] @f)))))

;; Forward declarations for resolvers (defined after load-env)
(declare create-expr-resolver create-name-resolver create-level-resolver resolve-ci-shell)

;; ============================================================
;; Load — reconstruct Env from persisted PSS
;; ============================================================

(defn contains-name-checker
  "Cheap declaration-presence predicate for a persisted branch.

   Returns (fn [name-string] boolean) that answers via PSS membership ONLY
   (sorted-set tree-node reads) — WITHOUT resolving the ConstantInfo's
   expression DAG from the store. Use for bulk presence tests (e.g. the
   attrs import over ~100k Mathlib names), where going through `env/lookup`
   would hydrate every hit and turn store open into minutes of IO."
  [store-map branch-name]
  (let [{:keys [storage store]} store-map
        branch-meta (store-get store [:branches branch-name])]
    (when branch-meta
      (let [env-pss (pss/restore-by name-cmp (:env-root branch-meta) storage)]
        (fn [name-str]
          (some? (pss/lookup env-pss [(ansatz-name/from-string name-str) nil])))))))

(defn- branch-loader
  "Create shared lazy branch lookup state.

   The returned lookup function is intentionally unrestricted. Callers that
   need admission-order visibility must wrap it before installing it into Env.
   Keeping this state shared avoids duplicate expression/name/level resolver
   caches between staged verifier lookup and declaration fetch.

   :value-policy :full (default) | :defs-only, and :keep-value? (name → bool) —
   see resolve-ci-shell. Verification must use :full."
  [store-map branch-name & {:keys [value-policy keep-value?] :or {value-policy :full}}]
  (let [{:keys [storage store]} store-map
        branch-meta (store-get store [:branches branch-name])]
    (when (nil? branch-meta)
      (throw (ex-info "Branch not found" {:branch branch-name})))
    (let [env-root (:env-root branch-meta)
          env-pss (pss/restore-by name-cmp env-root storage)
          dag? (:dag-storage? branch-meta)
          pss-dag? (and dag? (:exprs-root branch-meta))
          resolve-expr-fn
          (when dag?
            (if pss-dag?
              (let [exprs-pss (pss/restore-by id-cmp (:exprs-root branch-meta) storage)
                    names-pss (pss/restore-by id-cmp (:names-root branch-meta) storage)
                    levels-pss (pss/restore-by id-cmp (:levels-root branch-meta) storage)
                    resolve-name-fn (create-name-resolver names-pss)
                    resolve-level-fn (create-level-resolver levels-pss)]
                (create-expr-resolver exprs-pss resolve-name-fn resolve-level-fn))
              (let [resolve-name-fn (create-name-resolver store)
                    resolve-level-fn (create-level-resolver store)]
                (create-expr-resolver store resolve-name-fn resolve-level-fn))))
          lookup-ci (fn [^Name name]
                      (let [result (pss/lookup env-pss [name nil])]
                        (when result
                          (let [entry (nth result 1)]
                            (if dag?
                              (resolve-ci-shell entry resolve-expr-fn value-policy keep-value?)
                              entry)))))]
      {:branch-meta branch-meta
       :lookup-ci lookup-ci})))

(defn branch-resolver
  "An UNRESTRICTED `(fn [name-str] ConstantInfo|nil)` over a branch, with its own resolver
   caches — one per thread when resolving in parallel (the name/level caches are not
   thread-safe). Options as branch-loader: :value-policy :full|:defs-only, :keep-value?."
  [store-map branch-name & {:keys [value-policy keep-value?] :or {value-policy :full}}]
  (let [{:keys [lookup-ci]} (branch-loader store-map branch-name
                                           :value-policy value-policy :keep-value? keep-value?)]
    (fn [name-str] (lookup-ci (ansatz-name/from-string name-str)))))

(defn load-decl-order
  "The branch's declarations in export (admission) order, as name strings."
  [store-map branch-name]
  (let [{:keys [store]} store-map
        branch-meta (store-get store [:branches branch-name])]
    (when branch-meta
      (if-let [num-chunks (:decl-order-chunks branch-meta)]
        (into [] (mapcat (fn [i] (store-get store [:decl-order branch-name i]))) (range num-chunks))
        (store-get store [:decl-order branch-name])))))

(defn load-env
  "Load an Env from a persisted branch.
   Returns a lazy PSS-backed Env that loads declarations on demand.
   Only the PSS tree nodes needed for lookup are deserialized.
   For DAG-based storage, expressions are resolved from the store on demand.
   Supports two formats:
   - Full PSS (non-DAG): env-PSS holds ConstantInfo with full Expr objects
   - PSS DAG: dag-storage? + exprs-root → expr/name/level PSS trees

   Optional :visible? predicate restricts external lookup. Verification uses
   this to model Lean admission order: a declaration can only see admitted
   earlier declarations."
  [store-map branch-name & {:keys [visible? loader value-policy keep-value?]
                            :or {value-policy :full}}]
  (let [{:keys [branch-meta lookup-ci]} (or loader (branch-loader store-map branch-name
                                                                  :value-policy value-policy
                                                                  :keep-value? keep-value?))]
    (let [^Env env (Env.)]
      (let [env (if (:quot-enabled branch-meta) (.enableQuot env) env)
            env (if visible?
                  (.withExternalLookupFiltered env lookup-ci (int (:env-count branch-meta 0)) visible?)
                  (.withExternalLookup env lookup-ci (int (:env-count branch-meta 0))))]
        env))))

(defn resolve-expr
  "Look up a single expression by ID from the exprs PSS.
   Returns the raw byte[] (ExprStore binary format)."
  [store-map branch-name expr-id]
  (let [{:keys [storage store]} store-map
        branch-meta (k/get store [:branches branch-name] nil {:sync? true})]
    (when (nil? branch-meta)
      (throw (ex-info "Branch not found" {:branch branch-name})))
    (let [exprs-root (:exprs-root branch-meta)
          exprs-pss (pss/restore-by id-cmp exprs-root storage)
          result (pss/lookup exprs-pss [(long expr-id) nil])]
      (when result
        (nth result 1)))))

(defn load-names
  "Load all [id, Name] entries from the names PSS."
  [store-map branch-name]
  (let [{:keys [storage store]} store-map
        branch-meta (k/get store [:branches branch-name] nil {:sync? true})]
    (when (nil? branch-meta)
      (throw (ex-info "Branch not found" {:branch branch-name})))
    (let [names-root (:names-root branch-meta)
          names-pss (pss/restore-by id-cmp names-root storage)]
      (seq names-pss))))

;; ============================================================
;; Expression resolver — reconstruct Expr from DAG entries
;; ============================================================

(def ^:private binder-info-lut
  {0 (clojure.lang.Keyword/intern nil "default")
   1 (clojure.lang.Keyword/intern nil "implicit")
   2 (clojure.lang.Keyword/intern nil "strict-implicit")
   3 (clojure.lang.Keyword/intern nil "inst-implicit")})

(defn- pss-lookup-raw
  "Look up a value in a PSS by integer ID. Returns the value (second element) or nil."
  [pss id]
  (when-let [result (pss/lookup pss [(long id) nil])]
    (nth result 1)))

(defn create-expr-resolver
  "Create a function (resolve-expr id) → Expr that reads expression DAG entries
   and iteratively resolves sub-expression IDs.
   Uses an explicit work stack to avoid StackOverflowError on deep trees.
   source: either a PSS (for PSS DAG format) or a store (for flat DAG format).
   names-fn: int→Name, levels-fn: int→Level."
  [source names-fn levels-fn]
  (let [pss? (instance? PersistentSortedSet source)
        lookup-raw (if pss?
                     (fn [id] (pss-lookup-raw source id))
                     (fn [id] (store-get source [:expr id])))
        expr-cache-size (long-prop "ansatz.storage.expr-cache-size" 16384)
        ^java.util.Map cache (proxy [java.util.LinkedHashMap] [(int expr-cache-size) (float 0.75) true]
                               (removeEldestEntry [_entry]
                                 (> (.size ^java.util.Map this) expr-cache-size)))]
    (letfn [(decode-leaf [^bytes raw]
              (let [bb (java.nio.ByteBuffer/wrap raw)
                    tag (int (.get bb))]
                (case tag
                  0 [(Expr/bvar (.getLong bb)) nil]
                  1 (let [level-id (.getInt bb)
                          level (levels-fn level-id)]
                      [(Expr/sort level (Level/hasParam level)) nil])
                  2 (let [name-id (.getInt bb)
                          num-levels (bit-and (.getShort bb) 0xFFFF)
                          n (names-fn name-id)]
                      (if (zero? num-levels)
                        [(Expr/mkConst n java.util.Collections/EMPTY_LIST false) nil]
                        (let [lvls (object-array num-levels)
                              hp (loop [i 0 has-param false]
                                   (if (< i num-levels)
                                     (let [l (levels-fn (.getInt bb))]
                                       (aset lvls i l)
                                       (recur (inc i) (or has-param (Level/hasParam l))))
                                     has-param))]
                          [(Expr/mkConst n (java.util.Arrays/asList lvls) (boolean hp)) nil])))
                  3 (let [fn-id (long (.getInt bb))
                          arg-id (long (.getInt bb))]
                      [nil [:app fn-id arg-id]])
                  4 (let [bi (int (.get bb))
                          name-id (.getInt bb)
                          type-id (long (.getInt bb))
                          body-id (long (.getInt bb))]
                      [nil [:lam (names-fn name-id) (binder-info-lut bi) type-id body-id]])
                  5 (let [bi (int (.get bb))
                          name-id (.getInt bb)
                          type-id (long (.getInt bb))
                          body-id (long (.getInt bb))]
                      [nil [:forall (names-fn name-id) (binder-info-lut bi) type-id body-id]])
                  6 (let [name-id (.getInt bb)
                          type-id (long (.getInt bb))
                          value-id (long (.getInt bb))
                          body-id (long (.getInt bb))]
                      [nil [:let (names-fn name-id) type-id value-id body-id]])
                  7 (let [len (bit-and (.getShort bb) 0xFFFF)
                          bytes (byte-array len)]
                      (.get bb bytes)
                      [(Expr/litNat (java.math.BigInteger. bytes)) nil])
                  8 (let [len (.getInt bb)
                          bytes (byte-array len)]
                      (.get bb bytes)
                      [(Expr/litStr (String. bytes java.nio.charset.StandardCharsets/UTF_8)) nil])
                  9 (let [inner-id (long (.getInt bb))]
                      [nil [:mdata inner-id]])
                  10 (let [name-id (.getInt bb)
                           proj-idx (long (.getInt bb))
                           struct-id (long (.getInt bb))]
                       [nil [:proj (names-fn name-id) proj-idx struct-id]])
                  11 [(Expr/fvar (.getLong bb)) nil])))

            (assemble [op children]
              (case (first op)
                :app (Expr/app (nth children 0) (nth children 1))
                :lam (Expr/lam (nth op 1) (nth children 0) (nth children 1) (nth op 2))
                :forall (Expr/forall (nth op 1) (nth children 0) (nth children 1) (nth op 2))
                :let (Expr/mkLet (nth op 1) (nth children 0) (nth children 1) (nth children 2))
                :mdata (Expr/mdata nil (nth children 0))
                :proj (Expr/proj (nth op 1) (long (nth op 2)) (nth children 0))))

            (child-ids [op]
              (case (first op)
                :app [(nth op 1) (nth op 2)]
                :lam [(nth op 3) (nth op 4)]
                :forall [(nth op 3) (nth op 4)]
                :let [(nth op 2) (nth op 3) (nth op 4)]
                :mdata [(nth op 1)]
                :proj [(nth op 3)]))]

      (fn resolve-expr [id]
        (let [id (long id)]
          (or (.get cache (Long/valueOf id))
              (let [stack (java.util.ArrayDeque.)
                    result-stack (java.util.ArrayDeque.)]
                (.push stack [:resolve id])
                (while (not (.isEmpty stack))
                  (let [frame (.pop stack)
                        action (nth frame 0)]
                    (case action
                      :resolve
                      (let [rid (long (nth frame 1))
                            cached (.get cache (Long/valueOf rid))]
                        (if cached
                          (.push result-stack cached)
                          (let [^bytes raw (lookup-raw rid)]
                            (when (nil? raw)
                              (throw (ex-info "Expression not found in store" {:expr-id rid})))
                            (let [[leaf-result op] (decode-leaf raw)]
                              (if leaf-result
                                (do (set! (.-storeId ^Expr leaf-result) (int rid))
                                    (.put cache (Long/valueOf rid) leaf-result)
                                    (.push result-stack leaf-result))
                                (let [cids (child-ids op)]
                                  (.push stack [:assemble rid op (count cids)])
                                  (doseq [cid (reverse cids)]
                                    (.push stack [:resolve (long cid)]))))))))

                      :assemble
                      (let [rid (long (nth frame 1))
                            op (nth frame 2)
                            n-children (int (nth frame 3))
                            children (let [arr (object-array n-children)]
                                       (loop [i (dec n-children)]
                                         (when (>= i 0)
                                           (aset arr i (.pop result-stack))
                                           (recur (dec i))))
                                       (vec arr))
                            expr (assemble op children)]
                        (set! (.-storeId ^Expr expr) (int rid))
                        (.put cache (Long/valueOf rid) expr)
                        (.push result-stack expr)))))
                (.pop result-stack))))))))

(defn create-name-resolver
  "Create a function (resolve-name id) → Name.
   source: either a PSS (for PSS DAG format) or a store (for flat DAG format)."
  [source]
  (let [pss? (instance? PersistentSortedSet source)
        lookup-fn (if pss?
                    (fn [id] (pss-lookup-raw source id))
                    (fn [id] (store-get source [:name id])))
        ^java.util.Map cache (proxy [java.util.LinkedHashMap] [16384 (float 0.75) true]
                               (removeEldestEntry [_entry]
                                 (> (.size ^java.util.Map this) 131072)))]
    (fn [id]
      (let [id (long id)]
        (or (.get cache (Long/valueOf id))
            (let [n (lookup-fn id)]
              (when (nil? n)
                (throw (ex-info "Name not found in store" {:name-id id})))
              (.put cache (Long/valueOf id) n)
              n))))))

(defn create-level-resolver
  "Create a function (resolve-level id) → Level.
   source: either a PSS (for PSS DAG format) or a store (for flat DAG format)."
  [source]
  (let [pss? (instance? PersistentSortedSet source)
        lookup-fn (if pss?
                    (fn [id] (pss-lookup-raw source id))
                    (fn [id] (store-get source [:level id])))
        cache (java.util.HashMap. 8192)]
    (fn [id]
      (let [id (long id)]
        (or (.get cache (Long/valueOf id))
            (let [l (lookup-fn id)]
              (when (nil? l)
                (throw (ex-info "Level not found in store" {:level-id id})))
              (.put cache (Long/valueOf id) l)
              l))))))

(defn resolve-ci-shell
  "Resolve a CI-shell map to a full ConstantInfo by resolving expression IDs.

   `value-policy` (default :full): :defs-only skips the VALUE of theorems and opaques
   (tags 2/3). After admission the kernel never reads a theorem body — lean4#12973 made
   theorems opaque to delta and `ConstantInfo.getValue` is DEF-only — so a proving session
   skips the largest thing in the store (median proof 3,790 chars vs 709 for the statement,
   67 ms vs ~4 ms per cold lookup). `keep-value?` (name → bool) overrides :defs-only for
   individual names; verification and `prepare-verify` use :full."
  ([ci-shell resolve-expr-fn] (resolve-ci-shell ci-shell resolve-expr-fn :full nil))
  ([ci-shell resolve-expr-fn value-policy keep-value?]
   (let [m (if (instance? CIShell ci-shell) (.data ^CIShell ci-shell) ci-shell)
         tag (int (:tag m))
         type-expr (resolve-expr-fn (:type-id m))
         lps (into-array Object (:lps m))
        ;; THM (2) / OPAQUE (3) bodies are skipped under :defs-only unless kept by name
         skip-value? (and (= value-policy :defs-only)
                          (or (= tag 2) (= tag 3))
                          (not (and keep-value? (keep-value? (:name m)))))
         resolve-value (fn [id] (when-not skip-value? (resolve-expr-fn id)))]
     (case tag
      ;; AXIOM
       0 (ConstantInfo/mkAxiom (:name m) lps type-expr
                               (boolean (:unsafe? m)))
      ;; DEF
       1 (let [h (let [hints (:hints m)]
                   (cond
                     (= hints :opaque) ConstantInfo/HINTS_OPAQUE
                     (= hints :abbrev) ConstantInfo/HINTS_ABBREV
                     (map? hints) (:regular hints)
                     :else ConstantInfo/HINTS_OPAQUE))
               s (case (:safety m)
                   :safe (byte 0) :unsafe (byte 1) :partial (byte 2) (byte 0))]
           (ConstantInfo/mkDef (:name m) lps type-expr
                               (resolve-expr-fn (:value-id m))
                               (int h) s
                               (into-array Object (:all m))))
      ;; THM
       2 (ConstantInfo/mkThm (:name m) lps type-expr
                             (resolve-value (:value-id m))
                             (into-array Object (:all m)))
      ;; OPAQUE
       3 (ConstantInfo/mkOpaque (:name m) lps type-expr
                                (resolve-value (:value-id m))
                                (into-array Object (:all m))
                                (boolean (:unsafe? m)))
      ;; QUOT
       4 (ConstantInfo/mkQuot (:name m) lps type-expr (:quot-kind m))
      ;; INDUCT
       5 (ConstantInfo/mkInduct (:name m) lps type-expr
                                (int (:num-params m)) (int (:num-indices m))
                                (into-array Object (:all m))
                                (into-array Name (:ctors m))
                                (int (:num-nested m))
                                (boolean (:is-rec m))
                                (boolean (:is-reflexive m))
                                (boolean (:is-unsafe m)))
      ;; CTOR
       6 (ConstantInfo/mkCtor (:name m) lps type-expr
                              (:induct-name m)
                              (int (:cidx m))
                              (int (:num-params m))
                              (int (:num-fields m))
                              (boolean (:is-unsafe m)))
      ;; RECURSOR
       7 (let [rules (mapv (fn [r]
                             (ConstantInfo$RecursorRule.
                              (:ctor r) (int (:nfields r))
                              (resolve-expr-fn (:rhs-id r))))
                           (:rules m))]
           (ConstantInfo/mkRecursor (:name m) lps type-expr
                                    (into-array Object (:all m))
                                    (int (:num-params m))
                                    (int (:num-indices m))
                                    (int (:num-motives m))
                                    (int (:num-minors m))
                                    (into-array ConstantInfo$RecursorRule rules)
                                    (boolean (:is-k m))
                                    (boolean (:is-unsafe m))))))))

;; ============================================================
;; Branching
;; ============================================================

(defn fork-branch
  "Fork a branch — copies root addresses only (O(1), no data copied)."
  [store-map source-branch new-branch]
  (let [{:keys [store]} store-map
        branch-meta (k/get store [:branches source-branch] nil {:sync? true})]
    (when (nil? branch-meta)
      (throw (ex-info "Source branch not found" {:branch source-branch})))
    (let [forked (assoc branch-meta
                        :timestamp (System/currentTimeMillis)
                        :forked-from source-branch)]
      (k/assoc store [:branches new-branch] forked {:sync? true})
      forked)))

(defn list-branches
  "List all branches with their metadata."
  [store-map]
  (let [{:keys [store]} store-map
        key-metas (k/keys store {:sync? true})]
    (->> key-metas
         (map :key)
         (filter #(and (vector? %) (= :branches (first %))))
         (mapv (fn [k]
                 (let [meta (k/get store k nil {:sync? true})]
                   {:name (second k)
                    :timestamp (:timestamp meta)
                    :counts {:names (:names-count meta)
                             :levels (:levels-count meta)
                             :exprs (:exprs-count meta)
                             :env (:env-count meta)}}))))))

;; ============================================================
;; Streaming import — parse + persist in one pass
;; ============================================================

(defn import-ndjson-streaming!
  "Parse an ndjson file and persist CI-shells + expression DAG to LMDB.
   CI-shells (with expr IDs, not Expr objects) are stored in an env-PSS.
   Expressions, names, and levels are stored in PSS trees (bf=512).
   Memory-friendly: expressions stay in the file-backed ExprStore during parsing.
   Returns branch metadata.
   Progress is logged to :log-file (default /tmp/ansatz-import.log)."
  [store-map path branch-name & {:keys [verbose? max-count log-file]
                                 :or {verbose? false
                                      log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-import.log")}}]
  (let [{:keys [storage store settings-atom]} store-map
        start-time (System/currentTimeMillis)
        decl-order (atom (transient []))
        env-entries (atom (transient []))
        count-atom (atom 0)
        quot-enabled? (atom false)
        lw (java.io.FileWriter. (str log-file) false)]
    (log! lw "Streaming import of" path "into branch" (pr-str branch-name) "...")
    ;; Phase 1: Parse NDJSON, collect CI-shells
    (let [result (parser/parse-ndjson-file-streaming-raw
                  path
                  nil
                  (fn [_state ci-shell]
                    (let [n (swap! count-atom inc)]
                      (if (and max-count (> n max-count))
                        (reduced nil)
                        (let [ci-name (:name ci-shell)
                              name-str (.toString ^Name ci-name)]
                          (swap! env-entries conj! [ci-name (CIShell. ci-shell)])
                          (swap! decl-order conj! name-str)
                          (when (= 4 (:tag ci-shell))
                            (reset! quot-enabled? true))
                          (when (and verbose? (zero? (mod n 10000)))
                            (let [rt (Runtime/getRuntime)
                                  used (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                              (log! lw (str "  [" n "] " name-str " mem=" used "MB"))))
                          nil)))))
          parser-st (:parser-state result)
          ^ExprStore expr-store (:exprs parser-st)
          ^ArrayList names-al (:names parser-st)
          ^ArrayList levels-al (:levels parser-st)
          decl-count @count-atom
          order-vec (persistent! @decl-order)
          t1 (System/currentTimeMillis)]
      (log! lw "  Parsing done:" decl-count "declarations in" (- t1 start-time) "ms")

      ;; Phase 2: Build env-PSS from CI-shell entries
      (log! lw "  Building env-PSS...")
      (let [entries (persistent! @env-entries)
            sorted-entries (vec (sort-by (fn [[^Name n _]] (.toString n)) entries))
            _ (log! lw "  " (count sorted-entries) "sorted entries")
            [env-root env-count] (persist-pss! sorted-entries name-cmp storage "env")
            t2 (System/currentTimeMillis)]
        (log! lw "  env-PSS built:" (- t2 t1) "ms")

        ;; Phase 3: Build exprs-PSS incrementally (streaming, bf=512)
        (let [max-id (.maxId expr-store)]
          (log! lw "  Building exprs-PSS..." max-id "expressions (streaming, bf=512)")
          (let [[exprs-root exprs-count]
                (persist-pss-streaming!
                 max-id
                 (fn [i] (when-let [raw (try (.readRaw expr-store (int i))
                                             (catch Exception _ nil))]
                           [(long i) raw]))
                 id-cmp storage "exprs" lw
                 :branching-factor 512 :flush-interval 100000)
                t3 (System/currentTimeMillis)]
            (.close expr-store)
            (log! lw "  exprs-PSS built:" (- t3 t2) "ms")

            ;; Phase 4: Build names-PSS (in-memory, small enough)
            (log! lw "  Building names-PSS..." (.size names-al) "names")
            (let [name-entries (into []
                                     (for [i (range (.size names-al))
                                           :let [n (.get names-al i)]
                                           :when (some? n)]
                                       [(long i) n]))
                  [names-root names-count] (persist-pss! name-entries id-cmp storage "names"
                                                         :branching-factor 512)
                  t4 (System/currentTimeMillis)]
              (log! lw "  names-PSS built:" (- t4 t3) "ms")

              ;; Phase 5: Build levels-PSS (in-memory, small enough)
              (log! lw "  Building levels-PSS..." (.size levels-al) "levels")
              (let [level-entries (into []
                                        (for [i (range (.size levels-al))
                                              :let [l (.get levels-al i)]
                                              :when (some? l)]
                                          [(long i) l]))
                    [levels-root levels-count] (persist-pss! level-entries id-cmp storage "levels"
                                                             :branching-factor 512)
                    t5 (System/currentTimeMillis)]
                (log! lw "  levels-PSS built:" (- t5 t4) "ms")

                ;; Phase 6: Save metadata — chunk decl-order for large imports
                (let [chunk-size 10000
                      order-chunks (partition-all chunk-size order-vec)
                      num-chunks (count (seq order-chunks))]
                  (log! lw "  Saving decl-order:" (count order-vec) "entries in" num-chunks "chunks")
                  (doseq [[i chunk] (map-indexed vector order-chunks)]
                    (store-put store [:decl-order branch-name i] (vec chunk)))
                  (let [branch-meta {:env-root env-root
                                     :env-count env-count
                                     :exprs-root exprs-root
                                     :exprs-count exprs-count
                                     :names-root names-root
                                     :names-count names-count
                                     :levels-root levels-root
                                     :levels-count levels-count
                                     :quot-enabled @quot-enabled?
                                     :timestamp (System/currentTimeMillis)
                                     :dag-storage? true
                                     :decl-order-chunks num-chunks
                                     :decl-order-total (count order-vec)}]
                    (store-put store [:branches branch-name] branch-meta)
                    (let [elapsed (- (System/currentTimeMillis) start-time)]
                      (log! lw "Import done:" decl-count "declarations,"
                            max-id "expressions in" elapsed "ms")
                      (.close lw)
                      branch-meta)))))))))))

;; ============================================================
;; Large-stack thread helper
;; ============================================================

(def ^:private default-stack-size
  "64MB stack for deep type-checker recursion on large proofs."
  (* 64 1024 1024))

(defn- run-with-large-stack
  "Run f on a thread with a large stack (default 64MB).
   Blocks until completion. Re-throws any exception from f.
   The worker thread is a daemon and is interrupted if the calling thread is interrupted.
   Optional timeout-ms: if > 0, interrupts the thread once it has used that much CPU time
   (wall-clock only where thread CPU time is unsupported) and throws TimeoutException."
  ([f] (run-with-large-stack f default-stack-size 0))
  ([f stack-size] (run-with-large-stack f stack-size 0))
  ([f stack-size timeout-ms]
   (let [result (promise)
         error (promise)
         caller (Thread/currentThread)
         t (Thread. nil
                    (fn []
                      (try
                        (deliver result (f))
                        (catch Throwable e
                          (deliver error e))))
                    "ansatz-large-stack"
                    (long stack-size))]
     (.setDaemon t true)
     (.start t)
     (try
       (if (and timeout-ms (pos? timeout-ms))
         ;; The budget is the worker's CPU time, not wall-clock time: a verification run
         ;; that is SIGSTOPped while the machine is busy (or simply descheduled next to
         ;; other work) must not report the declaration in flight as timed out on resume.
         ;; Falls back to wall-clock only where the JVM cannot measure thread CPU time.
         (let [mx (java.lang.management.ManagementFactory/getThreadMXBean)
               tid (.getId t)
               budget-ns (* 1000000 (long timeout-ms))]
           (if (.isThreadCpuTimeSupported mx)
             (loop []
               (.join t 250)
               (when (.isAlive t)
                 (let [cpu (.getThreadCpuTime mx tid)]
                   (when (or (neg? cpu) (< cpu budget-ns))
                     (recur)))))
             (.join t (long timeout-ms))))
         (.join t))
       (catch InterruptedException _
         (.interrupt t)
         (.join t 5000)
         (throw (InterruptedException. "Interrupted while waiting for large-stack thread"))))
     (when (.isAlive t)
       (.interrupt t)
       (.join t 5000)
       (throw (java.util.concurrent.TimeoutException.
               (str "Declaration timed out after " timeout-ms "ms"))))
     (when (realized? error)
       (throw @error))
     @result)))

;; ============================================================
;; Verify from store — load + type-check in declaration order
;; ============================================================

(defn prepare-verify
  "Set up verification context for a branch. Returns a context map that can be
   passed to verify-batch! for incremental verification.
   Context: {:env Env, :decl-order vec, :resolve-fn (name-str → CI),
             :log-writer Writer, :ok atom, :errors atom, :error-names atom, :idx atom}"
  [store-map branch-name & {:keys [log-file append?]
                            :or {log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-verify.log")}}]
  (let [{:keys [store]} store-map
        lw (java.io.FileWriter. (str log-file) (boolean append?))
        loader (branch-loader store-map branch-name)
        {:keys [branch-meta lookup-ci]} loader]
    (let [decl-order (if-let [num-chunks (:decl-order-chunks branch-meta)]
                      ;; Chunked decl-order: reassemble from parts
                       (into [] (mapcat (fn [i] (store-get store [:decl-order branch-name i])))
                             (range num-chunks))
                      ;; Legacy: single value
                       (store-get store [:decl-order branch-name]))
          _ (when (nil? decl-order)
              (throw (ex-info "Declaration order not found" {:branch branch-name})))
          idx (atom 0)
          admitted-ranks (java.util.BitSet. (count decl-order))
          decl-ranks (java.util.HashMap. (* 2 (count decl-order)))
          _ (doseq [[i name-str] (map-indexed vector decl-order)]
              (.put decl-ranks (ansatz-name/from-string name-str) (long i)))
          visible? (fn [^Name name]
                     (when-let [rank (.get decl-ranks name)]
                       (let [rank (long rank)]
                         (and (< rank @idx)
                              (.get admitted-ranks (int rank))))))
          env (load-env store-map branch-name :visible? visible? :loader loader)
          ;; Verification type-checks against the staged env above, but fetching
          ;; the declaration being checked must be unrestricted. Both paths share
          ;; the branch loader so expression/name/level materialization caches
          ;; are not duplicated.
          resolve-fn (fn [name-str]
                       (let [name-obj (ansatz-name/from-string name-str)]
                         (lookup-ci name-obj)))]
      (log! lw "Prepared verification for branch" (pr-str branch-name)
            ":" (count decl-order) "declarations")
      {:env env
       :decl-order decl-order
       :resolve-fn resolve-fn
       :log-writer lw
       :ok (atom 0)
       :errors (atom 0)
       :error-names (atom [])
       :idx idx
       :admitted-ranks admitted-ranks
       :decl-ranks decl-ranks
       :start-time (System/currentTimeMillis)})))

(defn- mark-admitted-range!
  [ctx start-idx end-idx]
  (when-let [^java.util.BitSet admitted (:admitted-ranks ctx)]
    (when (< start-idx end-idx)
      (.set admitted (int start-idx) (int end-idx)))))

(def ^:private default-fuel
  "Default fuel per declaration for imported-store verification.
   Full Mathlib verification has legitimate declarations above 20M reduction
   steps (for example Polynomial.taylorLinearEquiv_symm used ~25.4M), so the
   store verifier defaults to 100M. Lower this explicitly for quick smoke runs.
   Set to 0 for unlimited (not recommended — tight loops become unkillable)."
  100000000)

(def ^:private verify-stack-size
  "256MB stack for deep isDefEq recursion on large Mathlib proofs.
   Lean's C++ has smaller stack frames so doesn't need this."
  (* 256 1024 1024))

(defn- same-name-array?
  [^objects xs ^objects ys]
  (and xs ys
       (= (alength xs) (alength ys))
       (loop [i 0]
         (cond
           (= i (alength xs)) true
           (= (aget xs i) (aget ys i)) (recur (inc i))
           :else false))))

(defn- bundle-all-names
  ^objects [^ConstantInfo ci]
  (or (.all ci) (into-array Object [(.name ci)])))

(defn- inductive-bundle-member?
  [^objects all-names ^ConstantInfo ci]
  (case (int (.tag ci))
    5 (boolean (some #(= ^Object % (.name ci)) all-names))
    6 (boolean (some #(= ^Object % (.inductName ci)) all-names))
    7 (same-name-array? all-names (.all ci))
    false))

(defn- build-inductive-bundle
  ^InductiveBundle [members]
  (let [inductives (filterv #(.isInduct ^ConstantInfo %) members)
        ctors (filterv #(.isCtor ^ConstantInfo %) members)
        recursors (filterv #(.isRecursor ^ConstantInfo %) members)
        ^ConstantInfo first-ind (first inductives)]
    (when-not first-ind
      (throw (ex-info "Inductive bundle has no inductive declarations"
                      {:members (mapv #(str (.name ^ConstantInfo %)) members)})))
    (InductiveBundle.
     (.levelParams first-ind)
     (.numParams first-ind)
     (.isUnsafe first-ind)
     (into-array ConstantInfo inductives)
     (into-array ConstantInfo ctors)
     (into-array ConstantInfo recursors))))

(defn- collect-inductive-bundle
  [decl-order resolve-fn start-idx ^ConstantInfo head-ci]
  (let [all-names (bundle-all-names head-ci)
        total (count decl-order)]
    (loop [j start-idx
           members []]
      (if (< j total)
        (let [name-str (nth decl-order j)
              ^ConstantInfo ci (resolve-fn name-str)]
          (when-not ci
            (throw (ex-info "Missing declaration while collecting inductive bundle"
                            {:idx j :name name-str})))
          (if (inductive-bundle-member? all-names ci)
            (recur (inc j) (conj members ci))
            {:members members :next-idx j}))
        {:members members :next-idx j}))))

(defn verify-one!
  "Verify the next declaration from ctx. Type checking runs on a large-stack
   thread (256MB) to handle deep isDefEq recursion.
   Returns result map with :status, :name, :fuel-used, :elapsed-ms. Non-inductive
   constants report measured fuel; inductive bundles currently report 0.
   Inductive declarations are verified as a contiguous Lean-style bundle.
   Failed declarations are not marked admitted unless `:admit-failures?` (the corpus run's
   choice, so a failure does not cascade into its dependents); non-stop mode is diagnostic."
  [ctx & {:keys [fuel timeout-ms admit-failures?] :or {fuel default-fuel timeout-ms 120000}}]
  (let [{:keys [env decl-order resolve-fn ok errors error-names idx]} ctx
        i @idx
        total (count decl-order)]
    (when (>= i total)
      (throw (ex-info "All declarations verified" {:idx i :total total})))
    (let [name-str (nth decl-order i)
          t0 (System/nanoTime)
          ^ConstantInfo ci (resolve-fn name-str)]
      (if (nil? ci)
        (do (swap! errors inc)
            (swap! error-names conj {:name name-str :error "MISSING"})
            (swap! idx inc)
            {:status :missing :name name-str :idx i})
        (let [bundle? (.isInduct ci)
              ;; collected OUTSIDE the try: a failed bundle head must still advance past its
              ;; members, or each constructor/recursor is then met alone and reported too
              {:keys [members next-idx]}
              (when bundle?
                (try (collect-inductive-bundle decl-order resolve-fn i ci)
                     (catch Throwable _ nil)))]
          (try
            (let [fuel-used
                  (long
                   (run-with-large-stack
                    (fn []
                      (cond
                        bundle?
                        (do
                          (TypeChecker/checkInductiveBundle
                           env (build-inductive-bundle members) (long fuel))
                          0)

                        (or (.isCtor ci) (.isRecursor ci))
                        (throw (ex-info "Inductive bundle member encountered outside bundle head"
                                        {:idx i :name name-str}))

                        :else
                        (TypeChecker/checkConstantFuel env ci (long fuel))))
                    verify-stack-size
                    timeout-ms))
                  elapsed-ms (/ (- (System/nanoTime) t0) 1e6)]
              (mark-admitted-range! ctx i (if bundle? next-idx (inc i)))
              (swap! ok + (if bundle? (count members) 1))
              (if bundle?
                (reset! idx next-idx)
                (swap! idx inc))
              (cond-> {:status :ok :name name-str :idx i
                       :fuel-used fuel-used :elapsed-ms elapsed-ms}
                bundle? (assoc :bundle-size (count members)
                               :next-idx next-idx)))
            (catch Throwable ex
              (let [msg (str (.getClass ex) ": " (.getMessage ex))
                    elapsed-ms (/ (- (System/nanoTime) t0) 1e6)
                    fuel-exceeded? (or (instance? OutOfMemoryError ex)
                                       (.contains ^String msg "fuel exhausted"))]
                (when (instance? OutOfMemoryError ex)
                  (System/gc))
                (swap! errors inc)
                (swap! error-names conj {:name name-str :error msg
                                         :fuel-exceeded? fuel-exceeded?})
              ;; A corpus run records the failure and ADMITS the declaration anyway: otherwise
              ;; the staged env hides it and every dependent fails as "Unknown constant" — one
              ;; timeout became 345 shadow failures. Dependents then get a real check modulo
              ;; the one recorded root, which `reverify-errors!` retries.
                (let [after (if (and bundle? next-idx) next-idx (inc i))]
                  (when admit-failures?
                    (mark-admitted-range! ctx i after))
                  (reset! idx after))
                {:status (if fuel-exceeded? :fuel-exceeded :error)
                 :name name-str :idx i
                 :error msg :elapsed-ms elapsed-ms}))))))))

(defn skip!
  "Advance idx by `n` without verifying. For resuming past known-good ranges.
   With PSS-backed external lookup, declarations are loaded on demand so we
   just advance the index. Quot is already enabled from branch metadata in load-env."
  [ctx n]
  (let [{:keys [idx decl-order]} ctx
        start-idx @idx
        end-idx (min (+ start-idx (long n)) (count decl-order))]
    (mark-admitted-range! ctx start-idx end-idx)
    (reset! idx end-idx)
    end-idx))

(defn find-decl
  "Find declaration indices matching a name substring (case-sensitive).
   Returns a vector of [index name-str] pairs."
  [ctx pattern]
  (let [{:keys [decl-order]} ctx]
    (into []
          (comp (map-indexed (fn [i n] [i n]))
                (filter (fn [[_ n]] (.contains ^String n ^String pattern))))
          decl-order)))

(defn skip-to!
  "Jump directly to index n. Alias for (reset! (:idx ctx) n)."
  [ctx n]
  (let [{:keys [idx decl-order]} ctx
        start-idx @idx
        n (min (long n) (count decl-order))]
    (mark-admitted-range! ctx start-idx n)
    (reset! idx n)
    n))

(defn verify-by-name!
  "Find a declaration by exact name and verify it.
   Jumps to its index, verifies one, then returns the result.
   Options are passed through to verify-one! (e.g. :fuel)."
  [ctx name-str & opts]
  (let [{:keys [decl-order]} ctx
        matches (into [] (comp (map-indexed (fn [i n] [i n]))
                               (filter (fn [[_ n]] (= n name-str))))
                      decl-order)]
    (when (empty? matches)
      (throw (ex-info "Declaration not found" {:name name-str})))
    (let [[i _] (first matches)]
      (skip-to! ctx i)
      (apply verify-one! ctx opts))))

(defn verify-batch!
  "Verify the next `n` declarations. Stops on first error by default.
   Returns summary map. The :last-result key holds the final verify-one! result
   (useful for inspecting errors).
   Options:
     :stop-on-error?  stop on first error (default true)
     :verbose?        log progress every 1000 decls (default false)
     :fuel            fuel limit (default 100M; 0 = unlimited)
     :timeout-ms      per-declaration wall-clock timeout
                      (default 120000, 0 disables)"
  [ctx n & {:keys [verbose? fuel timeout-ms stop-on-error? admit-failures?]
            :or {verbose? false fuel default-fuel timeout-ms 120000 stop-on-error? true}}]
  (let [{:keys [^java.io.Writer log-writer ok errors error-names idx decl-order]} ctx
        start-idx @idx
        end-idx (min (+ start-idx n) (count decl-order))
        batch-start (System/currentTimeMillis)
        max-fuel-used (atom 0)
        last-result (atom nil)]
    (loop []
      (when (< @idx end-idx)
        (let [result (verify-one! ctx :fuel fuel :timeout-ms timeout-ms :admit-failures? admit-failures?)]
          (reset! last-result result)
          (when (:fuel-used result)
            (swap! max-fuel-used max (:fuel-used result)))
          (when verbose?
            (case (:status result)
              (:ok) (when (zero? (mod (+ @ok @errors) 1000))
                      (let [rt (Runtime/getRuntime)
                            used (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                        (log! log-writer (str "  [" (+ @ok @errors) "] ok=" @ok
                                              " err=" @errors " mem=" used "MB"))))
              (:error :fuel-exceeded :missing)
              (log! log-writer (str "ERROR [" (:idx result) "] " (:name result)
                                    " - " (:error result)))))
          (when-not (and stop-on-error?
                         (#{:error :fuel-exceeded :missing} (:status result)))
            (recur)))))
    (let [elapsed (- (System/currentTimeMillis) batch-start)
          done? (>= @idx (count decl-order))]
      (log! log-writer (str "Batch [" start-idx ".." @idx "] done in " elapsed "ms"
                            " ok=" @ok " errors=" @errors
                            " maxFuel=" @max-fuel-used
                            (when done? " COMPLETE")))
      {:ok @ok :errors @errors :idx @idx
       :total (count decl-order) :done? done?
       :error-names @error-names
       :max-fuel-used @max-fuel-used
       :batch-elapsed-ms elapsed
       :last-result @last-result})))

(defn- checkpoint-file
  (^java.io.File [store-map branch] (checkpoint-file store-map branch nil))
  (^java.io.File [store-map branch slice]
   (io/file (:path store-map) (str "verify-" branch (when slice (str "-s" slice)) ".edn"))))

(defn- read-checkpoint
  "The checkpoint of `branch`: the combined file, else the union of the per-slice files a
   process-per-worker run writes (`verify-<branch>-s<i>.edn`), merged in slice order."
  [store-map branch]
  (let [f (checkpoint-file store-map branch)]
    (if (.exists f)
      (edn/read-string (slurp f))
      (let [parts (->> (.listFiles (io/file (:path store-map)))
                       (filter #(re-matches (re-pattern (str "verify-" branch "-s\\d+\\.edn")) (.getName ^java.io.File %)))
                       (map #(edn/read-string (slurp %)))
                       (sort-by :slice))]
        (when (seq parts)
          (assoc (first parts) :slices (mapv #(first (:slices %)) parts)))))))

(defn- save-checkpoint!
  "Write the checkpoint atomically (tmp + rename) — the file is the run's only durable state."
  [^java.io.File f cp]
  (let [tmp (io/file (str (.getPath f) ".tmp"))]
    (spit tmp (pr-str (assoc cp :updated (java.util.Date.))))
    (.renameTo tmp f)))

(defn- slice-starts
  "Contiguous slice boundaries over `total` declarations, each start moved FORWARD off an
   inductive bundle's constructors/recursors: a bundle is checked as one unit by the worker
   that owns its head, and a worker starting on a member alone would report an error."
  [decl-order resolve-fn workers]
  (let [total (count decl-order)
        size (quot total workers)
        head? (fn [j] (let [^ConstantInfo ci (resolve-fn (nth decl-order j))]
                        (not (and ci (or (.isCtor ci) (.isRecursor ci))))))
        align (fn [j] (loop [j j] (if (and (< j total) (not (head? j))) (recur (inc j)) j)))]
    (mapv (fn [i] (if (zero? i) 0 (align (* i size)))) (range workers))))

(defn verify-corpus!
  "Verify every declaration of `branch` — the authoritative full-corpus check — with `workers`
   contiguous slices in parallel, each CHECKPOINTED to <store>/verify-<branch>.edn every
   `checkpoint-every` declarations, so an interrupted run resumes (`:resume? true`, the default)
   where each slice stopped instead of starting over, and with failures RECORDED rather than
   fatal — a run over 700k declarations must not halt at the first one that needs more fuel
   (see `reverify-errors!`). A failed declaration is admitted for what follows, so the
   failure is counted once instead of cascading into every dependent as an unknown constant. A slice admits the declarations before it the way `skip-to!`
   does, so every declaration is still checked by exactly one worker against declarations that
   are themselves checked: completing all slices gives the sequential run's guarantee.
   Returns the checkpoint: {:total :ok :errors :error-names :done? :slices …}."
  [store-map branch & {:keys [workers resume? fuel timeout-ms checkpoint-every epoch-batches slice]
                       :or {workers 4 resume? true fuel default-fuel timeout-ms 120000
                            checkpoint-every 500 epoch-batches 20}}]
  ;; `:slice i` runs ONE of the `workers` slices in this process, checkpointed to its own file
  ;; (`verify-<branch>-s<i>.edn`): a worker per JVM, so a declaration whose check exhausts the
  ;; heap costs only its own worker (recorded as a failure) instead of dragging every other
  ;; worker into the same collector. A combined checkpoint from an earlier in-process run seeds
  ;; the slice when no per-slice file exists yet.
  (let [f (checkpoint-file store-map branch slice)
        saved (when resume?
                (cond (.exists f) (edn/read-string (slurp f))
                      slice (let [c (checkpoint-file store-map branch)]
                              (when (.exists c)
                                (let [all (edn/read-string (slurp c))]
                                  (assoc all :slices [(nth (:slices all) slice)]))))))
        worker-ids (if slice [slice] (range workers))
        worker-log (fn [i] (io/file (:path store-map) (str "verify-" branch "-w" i ".log")))
        ctxs (mapv (fn [i] (prepare-verify store-map branch :log-file (worker-log i))) worker-ids)
        decl-order (:decl-order (first ctxs))
        total (count decl-order)
        starts (slice-starts decl-order (:resolve-fn (first ctxs)) workers)
        ends (conj (subvec starts 1) total)
        all-slices (mapv (fn [s e] {:start s :end e :idx s :ok 0 :errors 0 :error-names []}) starts ends)
        fresh {:branch branch :workers workers :total total :done? false :slice slice
               :slices (if slice [(nth all-slices slice)] all-slices)}
        cp (atom (if (and saved (= (select-keys saved [:branch :workers :total])
                                   (select-keys fresh [:branch :workers :total])))
                   (assoc saved :done? false :slice slice)
                   fresh))
        t0 (System/currentTimeMillis)
        summarize (fn [c] (let [ss (:slices c)]
                            (assoc c :ok (reduce + (map :ok ss)) :errors (reduce + (map :errors ss))
                                   :error-names (into [] (mapcat :error-names) ss)
                                   :done? (every? #(>= (:idx %) (:end %)) ss)
                                   :elapsed-ms (- (System/currentTimeMillis) t0))))
        save! (fn [] (locking f (save-checkpoint! f (summarize @cp))))
        ;; A worker's context is rebuilt every `epoch-batches` batches: the store loader and the
        ;; env's shared reduction cache keep everything they ever resolved, and over a 700k-
        ;; declaration slice that grows into any heap and turns the run into garbage collection
        ;; (observed: 9 s batches became 600 s at the cap). prepare-verify is ~3 s.
        work (fn [i ctx0]
               (let [si (if slice 0 i)                      ; position of this worker's slice in cp
                     {:keys [end]} (nth (:slices @cp) si)]
                 (loop [ctx ctx0 batches 0]
                   (skip-to! ctx (:idx (nth (:slices @cp) si)))
                   (let [idx @(:idx ctx)]
                     (if (< idx end)
                       (let [o0 @(:ok ctx) e0 @(:errors ctx) n0 (count @(:error-names ctx))
                             r (verify-batch! ctx (min checkpoint-every (- end idx))
                                              :stop-on-error? false :admit-failures? true
                                              :fuel fuel :timeout-ms timeout-ms)]
                         (swap! cp update-in [:slices si]
                                (fn [sl] (-> sl
                                             (assoc :idx (:idx r))
                                             (update :ok + (- @(:ok ctx) o0))
                                             (update :errors + (- @(:errors ctx) e0))
                                             (update :error-names into (subvec (vec @(:error-names ctx)) n0)))))
                         (save!)
                         (if (< (inc batches) epoch-batches)
                           (recur ctx (inc batches))
                           (do (.close ^java.io.Writer (:log-writer ctx))
                               (recur (prepare-verify store-map branch :log-file (worker-log i) :append? true) 0))))
                       (.close ^java.io.Writer (:log-writer ctx)))))))]
    (save!)
    (try
      (run! deref (map (fn [i ctx] (future (work i ctx))) worker-ids ctxs))
      (finally
        (save!)))
    (summarize @cp)))

(defn reverify-errors!
  "Re-verify the declarations a `verify-corpus!` run recorded as failures — typically at a
   higher `:fuel` and longer `:timeout-ms` — one at a time, each against every earlier
   declaration admitted. Rewrites the checkpoint's error lists to what still fails. Returns
   {:fixed [names] :still-failing [{:name :error}]}."
  [store-map branch & {:keys [fuel timeout-ms] :or {fuel (* 10 default-fuel) timeout-ms 600000}}]
  (let [f (checkpoint-file store-map branch)
        cp (read-checkpoint store-map branch)
        ctx (prepare-verify store-map branch
                            :log-file (io/file (:path store-map) (str "verify-" branch "-retry.log")))
        ;; A constructor or recursor is only ever checked as part of its inductive's BUNDLE:
        ;; retry the bundle head, and let its verdict stand for every member recorded.
        head-of (fn [name]
                  (let [^ConstantInfo ci ((:resolve-fn ctx) name)
                        induct (cond
                                 (nil? ci) nil
                                 (.isCtor ci) (.inductName ci)
                                 ;; a recursor names no inductive directly; its first rule's
                                 ;; constructor does (an empty inductive has no rules — its
                                 ;; recursor keeps its own name and is retried as recorded)
                                 (.isRecursor ci) (some-> (.rules ci) first .ctor
                                                          ansatz-name/->string
                                                          ((:resolve-fn ctx)) .inductName))]
                    (if induct (ansatz-name/->string induct) name)))
        by-head (group-by (comp head-of :name) (:error-names cp))
        results (try
                  (into [] (mapcat (fn [[head entries]]
                                     (let [r (verify-by-name! ctx head :fuel fuel :timeout-ms timeout-ms)]
                                       (map (fn [{:keys [name]}] [name (:status r) (:error r)]) entries))))
                        by-head)
                  (finally (.close ^java.io.Writer (:log-writer ctx))))
        still (into [] (keep (fn [[n st err]] (when (not= st :ok) {:name n :error err}))) results)
        fixed (into [] (keep (fn [[n st _]] (when (= st :ok) n))) results)
        fixed? (set fixed)
        cp' (-> cp
                (update :slices (fn [ss] (mapv (fn [sl]
                                                 (let [keep (vec (remove #(fixed? (:name %)) (:error-names sl)))]
                                                   (assoc sl :error-names keep :errors (count keep))))
                                               ss)))
                (assoc :error-names still :errors (count still)))]
    (locking f (save-checkpoint! f cp'))
    {:fixed fixed :still-failing still}))

(defn verify-from-store!
  "Convenience: verify all declarations in one go.
   Uses verify-one!, which runs each declaration on a 256MB stack thread for
   deep kernel recursion.
   For interactive use, prefer prepare-verify + verify-one!/verify-batch!."
  [store-map branch-name & {:keys [verbose? log-file timeout-ms]
                            :or {verbose? false
                                 timeout-ms 120000
                                 log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-verify.log")}}]
  (run-with-large-stack
   (fn []
     (let [ctx (prepare-verify store-map branch-name :log-file log-file)
           total (count (:decl-order ctx))
           result (verify-batch! ctx total :verbose? verbose? :timeout-ms timeout-ms)]
       (.close ^java.io.Writer (:log-writer ctx))
       result))))

