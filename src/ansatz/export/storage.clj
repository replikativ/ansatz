;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; PSS-backed persistent store for Ansatz kernel.

(ns ansatz.export.storage
  "Durable persistence for Ansatz kernel state using PSS + konserve.

   Four PSS indices store names, levels, expressions, and environment
   declarations. Branching (forking) copies only root addresses — O(1)
   with full structural sharing.

   Storage stack: PSS → CachedStorage (IStorage) → konserve filestore."
  (:require [konserve.core :as k]
            [konserve.filestore :as fs]
            [konserve.serializers :as ser]
            [clojure.core.cache.wrapped :as cache]
            [org.replikativ.persistent-sorted-set :as pss]
            [ansatz.kernel.name :as ansatz-name]
            [ansatz.export.parser :as parser]
            [ansatz.export.types])
  (:import [ansatz.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule Env ExprStore TypeChecker FlatStore FlatStoreWriter FlatStoreWriter$DeclProvider]
           [ansatz.export.types CIShell]
           [org.replikativ.persistent_sorted_set PersistentSortedSet IStorage Leaf Branch Settings RefType]
           [org.fressian Writer Reader]
           [org.fressian.handlers WriteHandler ReadHandler]
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

;; ============================================================
;; Fressian handlers for Ansatz types
;; ============================================================

(defn- write-name [^Writer writer ^Name n]
  (.writeTag writer "ansatz.Name" 1)
  (case (int (.tag n))
    0 (.writeList writer [(int 0)])
    1 (.writeList writer [(int 1) (.prefix n) (.str n)])
    2 (.writeList writer [(int 2) (.prefix n) (.num n)])))

(defn- read-name [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)
        tag (int (nth parts 0))]
    (case tag
      0 Name/ANONYMOUS_NAME
      1 (Name/mkStr (nth parts 1) (nth parts 2))
      2 (Name/mkNum (nth parts 1) (long (nth parts 2))))))

(defn- write-level [^Writer writer ^Level l]
  (.writeTag writer "ansatz.Level" 1)
  (case (int (.tag l))
    0 (.writeList writer [(int 0)])
    1 (.writeList writer [(int 1) (.o0 l)])
    2 (.writeList writer [(int 2) (.o0 l) (.o1 l)])
    3 (.writeList writer [(int 3) (.o0 l) (.o1 l)])
    4 (.writeList writer [(int 4) (.o0 l)])))

(defn- read-level [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)
        tag (int (nth parts 0))]
    (case tag
      0 Level/ZERO_LEVEL
      1 (Level/succ (nth parts 1))
      2 (Level/max (nth parts 1) (nth parts 2))
      3 (Level/imax (nth parts 1) (nth parts 2))
      4 (Level/param (nth parts 1)))))

(defn- write-expr [^Writer writer ^Expr e]
  (.writeTag writer "ansatz.Expr" 1)
  (let [tag (int (.tag e))]
    (case tag
      0  (.writeList writer [0 (.longVal e)])                              ;; BVAR
      1  (.writeList writer [1 (.o0 e)])                                   ;; SORT
      2  (.writeList writer [2 (.o0 e) (.o1 e)])                           ;; CONST
      3  (.writeList writer [3 (.o0 e) (.o1 e)])                           ;; APP
      4  (.writeList writer [4 (.o0 e) (.o1 e) (.o2 e) (.o3 e)])          ;; LAM
      5  (.writeList writer [5 (.o0 e) (.o1 e) (.o2 e) (.o3 e)])          ;; FORALL
      6  (.writeList writer [6 (.o0 e) (.o1 e) (.o2 e) (.o3 e)])          ;; LET
      7  (.writeList writer [7 (.o0 e)])                                   ;; LIT_NAT
      8  (.writeList writer [8 (.o0 e)])                                   ;; LIT_STR
      9  (.writeList writer [9 (.o0 e) (.o1 e)])                           ;; MDATA
      10 (.writeList writer [10 (.o0 e) (.longVal e) (.o1 e)])             ;; PROJ
      11 (.writeList writer [11 (.longVal e)]))))                          ;; FVAR

(defn- read-expr [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)
        tag (int (nth parts 0))]
    (case tag
      0  (Expr/bvar (long (nth parts 1)))
      1  (let [l (nth parts 1)] (Expr/sort l (Level/hasParam l)))
      2  (let [n (nth parts 1)
               ls (nth parts 2)
               hp (some #(Level/hasParam %) ls)]
           (Expr/mkConst n ls (boolean hp)))
      3  (Expr/app (nth parts 1) (nth parts 2))
      4  (Expr/lam (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
      5  (Expr/forall (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
      6  (Expr/mkLet (nth parts 1) (nth parts 2) (nth parts 3) (nth parts 4))
      7  (Expr/litNat (nth parts 1))
      8  (Expr/litStr (nth parts 1))
      9  (Expr/mdata (nth parts 1) (nth parts 2))
      10 (Expr/proj (nth parts 1) (long (nth parts 2)) (nth parts 3))
      11 (Expr/fvar (long (nth parts 1))))))

(defn- write-recursor-rule [^Writer writer ^ConstantInfo$RecursorRule r]
  (.writeTag writer "ansatz.RecursorRule" 1)
  (.writeList writer [(.ctor r) (int (.nfields r)) (.rhs r)]))

(defn- read-recursor-rule [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)]
    (ConstantInfo$RecursorRule. (nth parts 0) (int (nth parts 1)) (nth parts 2))))

(defn- write-ci [^Writer writer ^ConstantInfo ci]
  (.writeTag writer "ansatz.ConstantInfo" 1)
  (let [tag (int (.tag ci))
        base [tag (.name ci) (vec (.levelParams ci)) (.type ci)]]
    (case tag
      0 (.writeList writer (conj base (.isUnsafe ci)))                ;; AXIOM
      1 (.writeList writer (conj base (.value ci) (int (.hints ci))   ;; DEF
                                 (int (.safety ci)) (vec (.all ci))))
      2 (.writeList writer (conj base (.value ci) (vec (.all ci))))   ;; THM
      3 (.writeList writer (conj base (.value ci) (vec (.all ci))     ;; OPAQUE
                                 (.isUnsafe ci)))
      4 (.writeList writer (conj base (.quotKind ci)))                ;; QUOT
      5 (.writeList writer (conj base (int (.numParams ci))           ;; INDUCT
                                 (int (.numIndices ci))
                                 (vec (.all ci))
                                 (vec (.ctors ci))
                                 (int (.numNested ci))
                                 (.isRec ci) (.isReflexive ci) (.isUnsafe ci)))
      6 (.writeList writer (conj base (.inductName ci)                ;; CTOR
                                 (int (.cidx ci))
                                 (int (.numParams ci))
                                 (int (.numFields ci))
                                 (.isUnsafe ci)))
      7 (.writeList writer (conj base (vec (.all ci))                 ;; RECURSOR
                                 (int (.numParams ci))
                                 (int (.numIndices ci))
                                 (int (.numMotives ci))
                                 (int (.numMinors ci))
                                 (vec (.rules ci))
                                 (.isK ci) (.isUnsafe ci))))))

(defn- read-ci [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)
        tag (int (nth parts 0))
        name (nth parts 1)
        lps (into-array Object (nth parts 2))
        type (nth parts 3)]
    (case tag
      0 (ConstantInfo/mkAxiom name lps type (boolean (nth parts 4)))
      1 (ConstantInfo/mkDef name lps type (nth parts 4)
                            (int (nth parts 5)) (byte (int (nth parts 6)))
                            (into-array Object (nth parts 7)))
      2 (ConstantInfo/mkThm name lps type (nth parts 4)
                            (into-array Object (nth parts 5)))
      3 (ConstantInfo/mkOpaque name lps type (nth parts 4)
                               (into-array Object (nth parts 5))
                               (boolean (nth parts 6)))
      4 (ConstantInfo/mkQuot name lps type (nth parts 4))
      5 (ConstantInfo/mkInduct name lps type
                               (int (nth parts 4)) (int (nth parts 5))
                               (into-array Object (nth parts 6))
                               (into-array Name (nth parts 7))
                               (int (nth parts 8))
                               (boolean (nth parts 9))
                               (boolean (nth parts 10))
                               (boolean (nth parts 11)))
      6 (ConstantInfo/mkCtor name lps type
                             (nth parts 4) (int (nth parts 5))
                             (int (nth parts 6)) (int (nth parts 7))
                             (boolean (nth parts 8)))
      7 (ConstantInfo/mkRecursor name lps type
                                 (into-array Object (nth parts 4))
                                 (int (nth parts 5)) (int (nth parts 6))
                                 (int (nth parts 7)) (int (nth parts 8))
                                 (into-array ConstantInfo$RecursorRule (nth parts 9))
                                 (boolean (nth parts 10))
                                 (boolean (nth parts 11))))))

;; ============================================================
;; CI-shell Fressian handlers
;; ============================================================

(defn- write-ci-shell [^Writer writer ^CIShell shell]
  (.writeTag writer "ansatz.CIShell" 1)
  (let [m (.data shell)
        tag (int (:tag m))]
    (case tag
      0 (.writeList writer [tag (:name m) (:lps m) (:type-id m) (:unsafe? m)])
      1 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:value-id m) (:hints m) (:safety m) (:all m)])
      2 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:value-id m) (:all m)])
      3 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:value-id m) (:all m) (:unsafe? m)])
      4 (.writeList writer [tag (:name m) (:lps m) (:type-id m) (:quot-kind m)])
      5 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:num-params m) (:num-indices m)
                            (:all m) (:ctors m) (:num-nested m)
                            (:is-rec m) (:is-reflexive m) (:is-unsafe m)])
      6 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:induct-name m) (:cidx m)
                            (:num-params m) (:num-fields m) (:is-unsafe m)])
      7 (.writeList writer [tag (:name m) (:lps m) (:type-id m)
                            (:all m) (:num-params m) (:num-indices m)
                            (:num-motives m) (:num-minors m)
                            (:rules m) (:is-k m) (:is-unsafe m)]))))

(defn- read-ci-shell [^Reader reader _tag _cnt]
  (let [parts (.readObject reader)
        tag (int (nth parts 0))
        name (nth parts 1)
        lps (nth parts 2)
        type-id (int (nth parts 3))]
    (CIShell.
     (case tag
       0 {:tag 0 :name name :lps lps :type-id type-id
          :unsafe? (boolean (nth parts 4))}
       1 {:tag 1 :name name :lps lps :type-id type-id
          :value-id (int (nth parts 4))
          :hints (nth parts 5) :safety (nth parts 6) :all (nth parts 7)}
       2 {:tag 2 :name name :lps lps :type-id type-id
          :value-id (int (nth parts 4)) :all (nth parts 5)}
       3 {:tag 3 :name name :lps lps :type-id type-id
          :value-id (int (nth parts 4)) :all (nth parts 5)
          :unsafe? (boolean (nth parts 6))}
       4 {:tag 4 :name name :lps lps :type-id type-id
          :quot-kind (nth parts 4)}
       5 {:tag 5 :name name :lps lps :type-id type-id
          :num-params (int (nth parts 4)) :num-indices (int (nth parts 5))
          :all (nth parts 6) :ctors (nth parts 7)
          :num-nested (int (nth parts 8))
          :is-rec (boolean (nth parts 9))
          :is-reflexive (boolean (nth parts 10))
          :is-unsafe (boolean (nth parts 11))}
       6 {:tag 6 :name name :lps lps :type-id type-id
          :induct-name (nth parts 4) :cidx (int (nth parts 5))
          :num-params (int (nth parts 6)) :num-fields (int (nth parts 7))
          :is-unsafe (boolean (nth parts 8))}
       7 {:tag 7 :name name :lps lps :type-id type-id
          :all (nth parts 4) :num-params (int (nth parts 5))
          :num-indices (int (nth parts 6)) :num-motives (int (nth parts 7))
          :num-minors (int (nth parts 8)) :rules (nth parts 9)
          :is-k (boolean (nth parts 10)) :is-unsafe (boolean (nth parts 11))}))))

;; ============================================================
;; PSS node Fressian handlers
;; ============================================================

(defn- make-pss-write-handlers []
  {Leaf
   {""
    (reify WriteHandler
      (write [_ writer leaf]
        (.writeTag writer "pss.Leaf" 1)
        (.writeObject writer (.keys ^Leaf leaf))))}

   Branch
   {""
    (reify WriteHandler
      (write [_ writer node]
        (.writeTag writer "pss.Branch" 1)
        (.writeObject writer {:level (.level ^Branch node)
                              :keys (.keys ^Branch node)
                              :addresses (.addresses ^Branch node)})))}

   Name
   {"" (reify WriteHandler (write [_ w v] (write-name w v)))}

   Level
   {"" (reify WriteHandler (write [_ w v] (write-level w v)))}

   Expr
   {"" (reify WriteHandler (write [_ w v] (write-expr w v)))}

   ConstantInfo
   {"" (reify WriteHandler (write [_ w v] (write-ci w v)))}

   ConstantInfo$RecursorRule
   {"" (reify WriteHandler (write [_ w v] (write-recursor-rule w v)))}

   CIShell
   {"" (reify WriteHandler (write [_ w v] (write-ci-shell w v)))}})

(defn- make-pss-read-handlers [settings-atom]
  {"pss.Leaf"
   (reify ReadHandler
     (read [_ reader _tag _cnt]
       (let [keys (.readObject reader)]
         (Leaf. ^List keys ^Settings @settings-atom))))

   "pss.Branch"
   (reify ReadHandler
     (read [_ reader _tag _cnt]
       (let [{:keys [keys level addresses]} (.readObject reader)]
         (Branch. (int level)
                  ^List keys
                  ^List addresses
                  ^Settings @settings-atom))))

   "ansatz.Name"
   (reify ReadHandler (read [_ r t c] (read-name r t c)))

   "ansatz.Level"
   (reify ReadHandler (read [_ r t c] (read-level r t c)))

   "ansatz.Expr"
   (reify ReadHandler (read [_ r t c] (read-expr r t c)))

   "ansatz.ConstantInfo"
   (reify ReadHandler (read [_ r t c] (read-ci r t c)))

   "ansatz.RecursorRule"
   (reify ReadHandler (read [_ r t c] (read-recursor-rule r t c)))

   "ansatz.CIShell"
   (reify ReadHandler (read [_ r t c] (read-ci-shell r t c)))})

;; ============================================================
;; CachedStorage (IStorage implementation)
;; ============================================================

(deftype CachedStorage [store cache pending-writes freed-addresses freelist settings-atom]
  IStorage
  (store [_ node]
    (let [;; Reuse a freed address if available, else generate new UUID
          reused (loop []
                   (let [current @freelist]
                     (if (empty? current)
                       nil
                       (let [addr (peek current)]
                         (if (compare-and-set! freelist current (pop current))
                           addr
                           (recur))))))
          address (or reused (UUID/randomUUID))]
      (when reused
        (cache/evict cache address))
      (swap! pending-writes conj [address node])
      (cache/miss cache address node)
      address))

  (restore [_ address]
    (if-let [cached (cache/lookup cache address)]
      (do (cache/hit cache address) cached)
      (let [node (k/get store address nil {:sync? true})]
        (when (nil? node)
          (throw (ex-info "Node not found in storage" {:address address})))
        (cache/miss cache address node)
        node)))

  (accessed [_ address]
    (cache/hit cache address)
    nil)

  (markFreed [_ address]
    (when address
      (swap! freed-addresses conj address)))

  (isFreed [_ address]
    (boolean (some #{address} @freed-addresses))))

(defn flush-writes!
  "Flush all pending writes to konserve.
   Writes in parallel batches for filestore."
  [storage]
  (let [^CachedStorage cs storage
        writes @(.pending-writes cs)
        kstore (.store cs)]
    (reset! (.pending-writes cs) [])
    (when (seq writes)
      (let [batch-size 64]
        (doseq [batch (partition-all batch-size writes)]
          (let [futures (mapv (fn [[addr node]]
                                (future (k/assoc kstore addr node {:sync? true})))
                              batch)]
            (doseq [f futures] @f)))))))

(defn gc-freed!
  "Recycle freed addresses to the freelist and evict them from cache.
   Freed addresses will be reused by subsequent store calls, avoiding disk bloat.
   For bulk imports with no concurrent readers, call after each flush."
  [storage]
  (let [^CachedStorage cs storage
        freed (loop []
                (let [current @(.freed-addresses cs)]
                  (if (compare-and-set! (.freed-addresses cs) current [])
                    current
                    (recur))))]
    (when (seq freed)
      ;; Evict from cache to prevent stale reads
      (doseq [addr freed]
        (cache/evict (.cache cs) addr))
      ;; Add to freelist for reuse
      (swap! (.freelist cs) into freed)
      (count freed))))

;; ============================================================
;; Store lifecycle
;; ============================================================

(defn open-store
  "Open a persistent store backed by a konserve filestore at dir-path.
   Returns a store map with :store (konserve), :storage (CachedStorage),
   and :settings-atom."
  [dir-path]
  (let [settings-atom (atom nil)
        read-handlers (make-pss-read-handlers settings-atom)
        write-handlers (make-pss-write-handlers)
        kstore (fs/connect-fs-store
                dir-path
                :opts {:sync? true}
                :config {:sync-blob? true}
                :serializers {:FressianSerializer
                              (ser/fressian-serializer
                               read-handlers
                               write-handlers)})
        lru-cache (cache/lru-cache-factory {} :threshold 4096)
        cached (->CachedStorage kstore lru-cache (atom []) (atom []) (atom []) settings-atom)
        settings (Settings. 64 RefType/WEAK)]
    (reset! settings-atom settings)
    {:store kstore
     :storage cached
     :settings-atom settings-atom}))

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
            (gc-freed! storage)
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
          (gc-freed! storage)
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

(defn load-env
  "Load an Env from a persisted branch.
   Returns a lazy PSS-backed Env that loads declarations on demand.
   Only the PSS tree nodes needed for lookup are deserialized.
   For DAG-based storage, expressions are resolved from the store on demand.
   Supports two formats:
   - Full PSS (non-DAG): env-PSS holds ConstantInfo with full Expr objects
   - PSS DAG: dag-storage? + exprs-root → expr/name/level PSS trees"
  [store-map branch-name]
  (let [{:keys [storage store]} store-map
        branch-meta (store-get store [:branches branch-name])]
    (when (nil? branch-meta)
      (throw (ex-info "Branch not found" {:branch branch-name})))
    (let [env-root (:env-root branch-meta)
          env-pss (pss/restore-by name-cmp env-root storage)
          dag? (:dag-storage? branch-meta)
          pss-dag? (and dag? (:exprs-root branch-meta))
          ;; For DAG storage, create expression resolver
          resolve-expr-fn
          (when dag?
            (if pss-dag?
              ;; PSS-based DAG: resolve from PSS trees
              (let [exprs-pss (pss/restore-by id-cmp (:exprs-root branch-meta) storage)
                    names-pss (pss/restore-by id-cmp (:names-root branch-meta) storage)
                    levels-pss (pss/restore-by id-cmp (:levels-root branch-meta) storage)
                    resolve-name-fn (create-name-resolver names-pss)
                    resolve-level-fn (create-level-resolver levels-pss)]
                (create-expr-resolver exprs-pss resolve-name-fn resolve-level-fn))
              ;; Flat DAG: resolve from flat LMDB entries
              (let [resolve-name-fn (create-name-resolver store)
                    resolve-level-fn (create-level-resolver store)]
                (create-expr-resolver store resolve-name-fn resolve-level-fn))))
          ^Env env (Env.)
          lookup-fn (fn [^Name name]
                      (let [result (pss/lookup env-pss [name nil])]
                        (when result
                          (let [entry (nth result 1)]
                            (if dag?
                              (resolve-ci-shell entry resolve-expr-fn)
                              entry)))))]
      (let [env (if (:quot-enabled branch-meta) (.enableQuot env) env)
            env (.withExternalLookup env lookup-fn (int (:env-count branch-meta 0)))]
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
        ^java.util.Map cache (proxy [java.util.LinkedHashMap] [16384 (float 0.75) true]
                               (removeEldestEntry [_entry]
                                 (> (.size ^java.util.Map this) 16384)))]
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
  "Resolve a CI-shell map to a full ConstantInfo by resolving expression IDs."
  [ci-shell resolve-expr-fn]
  (let [m (if (instance? CIShell ci-shell) (.data ^CIShell ci-shell) ci-shell)
        tag (int (:tag m))
        type-expr (resolve-expr-fn (:type-id m))
        lps (into-array Object (:lps m))]
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
                            (resolve-expr-fn (:value-id m))
                            (into-array Object (:all m)))
      ;; OPAQUE
      3 (ConstantInfo/mkOpaque (:name m) lps type-expr
                               (resolve-expr-fn (:value-id m))
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
                                   (boolean (:is-unsafe m)))))))

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
   Optional timeout-ms: if > 0, interrupts the thread after that many ms and throws TimeoutException."
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
         (.join t (long timeout-ms))
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
  [store-map branch-name & {:keys [log-file]
                            :or {log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-verify.log")}}]
  (let [{:keys [storage store]} store-map
        lw (java.io.FileWriter. (str log-file) false)
        branch-meta (store-get store [:branches branch-name])]
    (when (nil? branch-meta)
      (throw (ex-info "Branch not found" {:branch branch-name})))
    (let [decl-order (if-let [num-chunks (:decl-order-chunks branch-meta)]
                      ;; Chunked decl-order: reassemble from parts
                       (into [] (mapcat (fn [i] (store-get store [:decl-order branch-name i])))
                             (range num-chunks))
                      ;; Legacy: single value
                       (store-get store [:decl-order branch-name]))
          _ (when (nil? decl-order)
              (throw (ex-info "Declaration order not found" {:branch branch-name})))
          env (load-env store-map branch-name)
          ;; Delegate to env.lookup() which already has PSS-backed external lookup
          ;; from load-env. This avoids creating a duplicate PSS tree that would
          ;; accumulate deserialized nodes and grow memory unboundedly.
          resolve-fn (fn [name-str]
                       (let [name-obj (ansatz-name/from-string name-str)]
                         (.lookup ^Env env name-obj)))]
      (log! lw "Prepared verification for branch" (pr-str branch-name)
            ":" (count decl-order) "declarations")
      {:env env
       :decl-order decl-order
       :resolve-fn resolve-fn
       :log-writer lw
       :ok (atom 0)
       :errors (atom 0)
       :error-names (atom [])
       :idx (atom 0)
       :start-time (System/currentTimeMillis)})))

(def ^:private default-fuel
  "Default fuel per declaration. 20M steps is enough for all known mathlib proofs
   (heaviest legitimate batch used ~6M). Acts as a safety net against divergent
   computation while keeping the REPL responsive.
   Set to 0 for unlimited (not recommended — tight loops become unkillable)."
  20000000)

(def ^:private verify-stack-size
  "256MB stack for deep isDefEq recursion on large Mathlib proofs.
   Lean's C++ has smaller stack frames so doesn't need this."
  (* 256 1024 1024))

(defn verify-one!
  "Verify the next declaration from ctx. Type checking runs on a large-stack
   thread (256MB) to handle deep isDefEq recursion.
   Returns result map with :status, :name, :fuel-used, :elapsed-ms.
   Declarations that exceed fuel are added to env without full check
   and flagged :fuel-exceeded."
  [ctx & {:keys [fuel timeout-ms] :or {fuel default-fuel timeout-ms 120000}}]
  (let [{:keys [env decl-order resolve-fn ^java.io.Writer log-writer
                ok errors error-names idx]} ctx
        i @idx
        total (count decl-order)]
    (when (>= i total)
      (throw (ex-info "All declarations verified" {:idx i :total total})))
    (let [name-str (nth decl-order i)
          t0 (System/nanoTime)
          ^ConstantInfo ci (resolve-fn name-str)
          env-vol (volatile! env)]
      (if (nil? ci)
        (do (swap! errors inc)
            (swap! error-names conj {:name name-str :error "MISSING"})
            (swap! idx inc)
            {:status :missing :name name-str :idx i})
        (let [tag (.tag ci)]
          (try
            (let [raw-result
                  (run-with-large-stack
                   (fn []
                     (case (int tag)
                       4 ;; QUOT — no check needed
                       (do (vreset! env-vol (.enableQuot (.addConstant @env-vol ci))) 0)
                       (5 6 7) ;; INDUCT, CTOR, RECURSOR — check type only
                       (do (TypeChecker/checkType @env-vol ci (long fuel))
                           (vreset! env-vol (.addConstant @env-vol ci)) 0)
                       ;; DEF, THM, OPAQUE, AXIOM — full check with fuel+stats instrumentation
                       (let [result (TypeChecker/checkConstantFuelStats @env-vol ci (long fuel))]
                         (vreset! env-vol (.addConstantIfAbsent @env-vol ci))
                         result)))
                   verify-stack-size
                   timeout-ms)
                  elapsed-ms (/ (- (System/nanoTime) t0) 1e6)
                  ;; Extract stats when available (Object[4] from checkConstantFuelStats)
                  has-stats? (.isArray (class raw-result))
                  fuel-used (if has-stats? (long (aget ^objects raw-result 0)) (long raw-result))
                  stats (when has-stats? (into {} (aget ^objects raw-result 1)))
                  trace (when has-stats? (vec (aget ^objects raw-result 2)))
                  err-msg (when has-stats? (aget ^objects raw-result 3))]
              (if err-msg
                ;; Error with stats (fuel exhaustion, type mismatch, etc.)
                (let [fuel-exceeded? (.contains ^String err-msg "fuel exhausted")]
                  (try (vreset! env-vol (.addConstantIfAbsent @env-vol ci)) (catch Exception _))
                  (swap! errors inc)
                  (swap! error-names conj {:name name-str :error err-msg
                                           :fuel-exceeded? fuel-exceeded?})
                  (swap! idx inc)
                  (cond-> {:status (if fuel-exceeded? :fuel-exceeded :error)
                           :name name-str :idx i :error err-msg
                           :fuel-used fuel-used :elapsed-ms elapsed-ms}
                    stats (assoc :stats stats)
                    trace (assoc :trace trace)))
                ;; Success
                (do (swap! ok inc)
                    (swap! idx inc)
                    (cond-> {:status :ok :name name-str :idx i
                             :fuel-used fuel-used :elapsed-ms elapsed-ms}
                      stats (assoc :stats stats)
                      trace (assoc :trace trace)))))
            (catch Throwable ex
              (let [msg (str (.getClass ex) ": " (.getMessage ex))
                    elapsed-ms (/ (- (System/nanoTime) t0) 1e6)]
                (when (instance? OutOfMemoryError ex)
                  (System/gc)) ;; try to recover
                (try (vreset! env-vol (.addConstantIfAbsent @env-vol ci)) (catch Exception _))
                (swap! errors inc)
                (swap! error-names conj {:name name-str :error msg
                                         :fuel-exceeded? (instance? OutOfMemoryError ex)})
                (swap! idx inc)
                {:status :error :name name-str :idx i
                 :error msg :elapsed-ms elapsed-ms}))))))))

(defn skip!
  "Advance idx by `n` without verifying. For resuming past known-good ranges.
   With PSS-backed external lookup, declarations are loaded on demand so we
   just advance the index. Quot is already enabled from branch metadata in load-env."
  [ctx n]
  (let [{:keys [idx decl-order]} ctx
        end-idx (min (+ @idx (long n)) (count decl-order))]
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
        n (min (long n) (count decl-order))]
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
     :fuel            fuel limit (default 0 = unlimited)"
  [ctx n & {:keys [verbose? fuel stop-on-error?]
            :or {verbose? false fuel default-fuel stop-on-error? true}}]
  (let [{:keys [^java.io.Writer log-writer ok errors error-names idx decl-order]} ctx
        start-idx @idx
        end-idx (min (+ start-idx n) (count decl-order))
        batch-start (System/currentTimeMillis)
        max-fuel-used (atom 0)
        last-result (atom nil)]
    (loop []
      (when (< @idx end-idx)
        (let [result (verify-one! ctx :fuel fuel)]
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

(defn verify-from-store!
  "Convenience: verify all declarations in one go.
   Runs on a 64MB stack thread for deep recursion.
   For interactive use, prefer prepare-verify + verify-one!/verify-batch!."
  [store-map branch-name & {:keys [verbose? log-file]
                            :or {verbose? false
                                 log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-verify.log")}}]
  (run-with-large-stack
   (fn []
     (let [ctx (prepare-verify store-map branch-name :log-file log-file)
           total (count (:decl-order ctx))
           result (verify-batch! ctx total :verbose? verbose?)]
       (.close ^java.io.Writer (:log-writer ctx))
       result))))

;; ============================================================
;; FlatStore — mmap'd flat store import and verification
;; ============================================================

(defn import-to-flatstore!
  "Parse an ndjson file and write directly to FlatStore format.
   Bypasses PSS entirely — no LMDB needed.
   Returns the output directory path."
  [ndjson-path out-dir & {:keys [max-count log-file]
                          :or {log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-import.log")}}]
  (let [lw (java.io.FileWriter. (str log-file) false)
        start-time (System/currentTimeMillis)
        decl-order (atom (transient []))
        ci-shells (atom (transient {}))
        count-atom (atom 0)]
    (log! lw "FlatStore import of" ndjson-path "into" (str out-dir) "...")

    ;; Phase 1: Parse NDJSON
    (let [result (parser/parse-ndjson-file-streaming-raw
                  ndjson-path
                  nil
                  (fn [_state ci-shell]
                    (let [n (swap! count-atom inc)]
                      (if (and max-count (> n max-count))
                        (reduced nil)
                        (let [ci-name (:name ci-shell)
                              name-str (.toString ^Name ci-name)]
                          (swap! ci-shells assoc! name-str ci-shell)
                          (swap! decl-order conj! name-str)
                          (when (zero? (mod n 50000))
                            (log! lw (str "  parsed: " n)))
                          nil)))))
          parser-st (:parser-state result)
          ^ExprStore expr-store (:exprs parser-st)
          ^ArrayList names-al (:names parser-st)
          ^ArrayList levels-al (:levels parser-st)
          order-vec (persistent! @decl-order)
          shells (persistent! @ci-shells)
          t1 (System/currentTimeMillis)]
      (log! lw "  Parsing done:" @count-atom "declarations,"
            (.maxId expr-store) "expressions in" (- t1 start-time) "ms")

      ;; Phase 2: Build name→id index
      (log! lw "  Building name index...")
      (let [name-index (java.util.HashMap. (.size names-al))
            _ (dotimes [i (.size names-al)]
                (let [n (.get names-al i)]
                  (when n (.put name-index n (int i)))))
            ;; DeclProvider that creates ConstantInfo from CI shells
            ;; using dummy Expr objects with storeId set
            make-stub-expr (fn [expr-id]
                             (when (and expr-id (>= (int expr-id) 0))
                               (doto ^Expr (Expr/bvar 0)
                                 (-> .-storeId (set! (int expr-id))))))
            decl-provider (reify FlatStoreWriter$DeclProvider
                            (lookup [_ name]
                              (when-let [m (get shells (.toString name))]
                                (let [tag (int (:tag m))
                                      type-expr (make-stub-expr (:type-id m))
                                      lps (into-array Object (:lps m))]
                                  (case tag
                                    0 (ConstantInfo/mkAxiom (:name m) lps type-expr
                                                            (boolean (:unsafe? m)))
                                    1 (let [h (let [hints (:hints m)]
                                                (cond
                                                  (= hints :opaque) ConstantInfo/HINTS_OPAQUE
                                                  (= hints :abbrev) ConstantInfo/HINTS_ABBREV
                                                  (map? hints) (:regular hints)
                                                  :else ConstantInfo/HINTS_OPAQUE))
                                            s (case (:safety m)
                                                :safe (byte 0) :unsafe (byte 1) :partial (byte 2) (byte 0))]
                                        (ConstantInfo/mkDef (:name m) lps type-expr
                                                            (make-stub-expr (:value-id m))
                                                            (int h) s
                                                            (into-array Object (:all m))))
                                    2 (ConstantInfo/mkThm (:name m) lps type-expr
                                                          (make-stub-expr (:value-id m))
                                                          (into-array Object (:all m)))
                                    3 (ConstantInfo/mkOpaque (:name m) lps type-expr
                                                             (make-stub-expr (:value-id m))
                                                             (into-array Object (:all m))
                                                             (boolean (:unsafe? m)))
                                    4 (ConstantInfo/mkQuot (:name m) lps type-expr (:quot-kind m))
                                    5 (ConstantInfo/mkInduct (:name m) lps type-expr
                                                             (int (:num-params m)) (int (:num-indices m))
                                                             (into-array Object (:all m))
                                                             (into-array Name (:ctors m))
                                                             (int (:num-nested m))
                                                             (boolean (:is-rec m))
                                                             (boolean (:is-reflexive m))
                                                             (boolean (:is-unsafe m)))
                                    6 (ConstantInfo/mkCtor (:name m) lps type-expr
                                                           (:induct-name m)
                                                           (int (:cidx m))
                                                           (int (:num-params m))
                                                           (int (:num-fields m))
                                                           (boolean (:is-unsafe m)))
                                    7 (let [rules (mapv (fn [r]
                                                          (ConstantInfo$RecursorRule.
                                                           (:ctor r) (int (:nfields r))
                                                           (make-stub-expr (:rhs-id r))))
                                                        (:rules m))]
                                        (ConstantInfo/mkRecursor (:name m) lps type-expr
                                                                 (into-array Object (:all m))
                                                                 (int (:num-params m))
                                                                 (int (:num-indices m))
                                                                 (int (:num-motives m))
                                                                 (int (:num-minors m))
                                                                 (into-array ConstantInfo$RecursorRule rules)
                                                                 (boolean (:is-k m))
                                                                 (boolean (:is-unsafe m)))))))))]
        ;; Phase 3: Write FlatStore
        (log! lw "  Writing FlatStore...")
        (let [out-path (java.nio.file.Paths/get (str out-dir) (into-array String []))]
          (FlatStoreWriter/convert
           out-path
           expr-store
           names-al
           levels-al
           decl-provider
           (into-array String order-vec)
           name-index)
          ;; Write name-ids.data for exact Name lookup (avoids fromString issues)
          (let [name-ids (int-array (count order-vec))]
            (dotimes [i (count order-vec)]
              (let [ci-shell (get shells (nth order-vec i))
                    ^Name n (:name ci-shell)
                    id (when n (.get ^java.util.HashMap name-index n))]
                (aset name-ids i (int (if id id -1)))))
            (FlatStoreWriter/writeDeclNameIds
             (.resolve out-path "name-ids.data") name-ids)))
        (.close expr-store)
        (let [elapsed (- (System/currentTimeMillis) start-time)]
          (log! lw "FlatStore import done in" elapsed "ms")
          (.close lw)
          (str out-dir))))))

(defn open-flatstore
  "Open a FlatStore directory and return {::flat-store store, :env Env}."
  [dir-path]
  (let [store (FlatStore/open (java.nio.file.Paths/get (str dir-path) (into-array String [])))]
    {::flat-store store
     :env (.createEnv store)
     :decl-order (vec (.getDeclOrder store))}))

(defn prepare-verify-flat
  "Set up verification context from a FlatStore.
   Returns a context map compatible with verify-batch! and verify-one!."
  [flat-store-path & {:keys [log-file]
                      :or {log-file (str (System/getProperty "java.io.tmpdir") "/ansatz-verify.log")}}]
  (let [lw (java.io.FileWriter. (str log-file) false)
        {:keys [env decl-order] :as fs-map} (open-flatstore flat-store-path)
        ^FlatStore store (::flat-store fs-map)
        ;; Build name-str → Name lookup using getDeclName (handles special chars)
        name-lookup (let [m (java.util.HashMap. (count decl-order))]
                      (dotimes [i (count decl-order)]
                        (.put m (nth decl-order i) (.getDeclName store (int i))))
                      m)
        resolve-fn (fn [name-str]
                     (let [^Name name-obj (.get ^java.util.HashMap name-lookup name-str)]
                       (when name-obj
                         (.lookupDecl store name-obj))))]
    (log! lw "Prepared FlatStore verification:" (count decl-order) "declarations,"
          (.getExprCount store) "expressions")
    {:env env
     :decl-order decl-order
     :resolve-fn resolve-fn
     :log-writer lw
     :ok (atom 0)
     :errors (atom 0)
     :error-names (atom [])
     :idx (atom 0)
     :start-time (System/currentTimeMillis)
     ::flat-store store}))
