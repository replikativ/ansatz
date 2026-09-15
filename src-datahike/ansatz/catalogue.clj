(ns ansatz.catalogue
  "The store CATALOGUE: a datahike DB at `<store>/catalogue` holding the facts a prover reads
   about declarations — name, kind, universe/binder counts, the conclusion head, the ids of
   the statement and value in the term store, module and docstring, attributes, instance
   class/priority, the conclusion disc-tree key (`:decl/dt-key`), the @[simp] LHS keys
   (`:decl/simp-key`), and the REFS `:decl/mentions` (constants of the statement),
   `:decl/depends-on` (constants of the value) and `:decl/instance-of` — with the DURABLE
   disc-tree secondary index
   (ansatz.index.discr) as two instances: `:idx/dt` for recall, `:idx/simp` for simp. Built
   ONCE by the importer (ansatz.import) from the recall and simp keys in a single transaction;
   afterwards a fresh process `connect`s in ~130 ms and answers structural queries from
   persisted chunks — nothing is rebuilt per session. The in-memory tries (ansatz.recall,
   ansatz.simp-index) remain the fallback when a store has no catalogue.

   Lives under src-datahike (the `:datahike` alias): ansatz proper never depends on datahike;
   ansatz.recall reaches this namespace by `requiring-resolve` and degrades when absent."
  (:require [datahike.api :as d]
            [datahike.migrate :as migrate]
            [datahike.migrate.cbor :as mcbor]
            [datahike.migrate.digest :as dig]
            [ansatz.index.discr :as dti]
            [clojure.edn :as edn]
            [clojure.java.io :as io]))

(defn catalogue-dir ^java.io.File [store-path] (io/file store-path "catalogue"))

(defn config
  "datahike config for the catalogue of the store at `store-path` (file backend; the `:id` the
   file backend requires is derived from the path so reconnects agree)."
  [store-path]
  {:store {:backend :file
           :path (.getPath (catalogue-dir store-path))
           :id (java.util.UUID/nameUUIDFromBytes (.getBytes (str "ansatz.catalogue/" store-path) "UTF-8"))}
   :index :datahike.index/persistent-set
   :schema-flexibility :write
   :keep-history? false})

(def schema-tx
  "One entity per declaration. Scalars first; the REFS (mentions, depends-on, instance-of) are
   what makes it a database rather than an index — dependents, co-mentions and module slices
   are joins. :db/index on the attributes searched by value."
  [{:db/ident :decl/name :db/valueType :db.type/string :db/cardinality :db.cardinality/one
    :db/unique :db.unique/identity}
   {:db/ident :decl/kind :db/valueType :db.type/keyword :db/cardinality :db.cardinality/one :db/index true}
   {:db/ident :decl/num-univs :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/num-binders :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/concl-head :db/valueType :db.type/string :db/cardinality :db.cardinality/one :db/index true}
   {:db/ident :decl/type-id :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/value-id :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/module :db/valueType :db.type/string :db/cardinality :db.cardinality/one :db/index true}
   {:db/ident :decl/doc :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
   {:db/ident :decl/attr :db/valueType :db.type/string :db/cardinality :db.cardinality/many :db/index true}
   {:db/ident :decl/simp-prio :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/instance-prio :db/valueType :db.type/long :db/cardinality :db.cardinality/one}
   {:db/ident :decl/dt-key :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
   {:db/ident :decl/simp-key :db/valueType :db.type/string :db/cardinality :db.cardinality/many}
   ;; refs
   {:db/ident :decl/instance-of :db/valueType :db.type/ref :db/cardinality :db.cardinality/one}
   {:db/ident :decl/mentions :db/valueType :db.type/ref :db/cardinality :db.cardinality/many}
   {:db/ident :decl/depends-on :db/valueType :db.type/ref :db/cardinality :db.cardinality/many}])

(def index-tx
  [{:db/ident :idx/dt :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/dt-key]}
   {:db/ident :idx/simp :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/simp-key]}])

(defn- scalar-entities
  "One entity map per declaration name from every source, scalars only (refs come second, once
   the entities exist), in declaration order."
  [{:keys [recall-keys simp-keys facts modules attrs instances]}]
  ;; DECLARATION ORDER, deliberately: entities are transacted in this order, so their ids are
  ;; contiguous per facts chunk, so each chunk's ref batch touches a contiguous range of the
  ;; entity-sorted indices instead of every leaf (HashMap order scattered the ids and each
  ;; 500k-datom commit rewrote the whole tree: 15 GB of superseded nodes for Mathlib).
  (let [by-name (java.util.LinkedHashMap.)
        ent! (fn [n f] (.put by-name n (f (or (.get by-name n) {:decl/name n}))))]
    (doseq [f facts]
      (ent! (:name f) #(cond-> (assoc % :decl/kind (:kind f) :decl/num-univs (:num-univs f)
                                      :decl/num-binders (:num-binders f) :decl/type-id (:type-id f))
                        (:concl-head f) (assoc :decl/concl-head (:concl-head f))
                        (:value-id f) (assoc :decl/value-id (:value-id f)))))
    (doseq [[n k] recall-keys] (ent! n #(assoc % :decl/dt-key k)))
    (doseq [[n k] simp-keys] (ent! n #(update % :decl/simp-key (fnil conj #{}) k)))
    (doseq [[n {:keys [module doc]}] modules :when (.containsKey by-name n)]
      (ent! n #(cond-> (assoc % :decl/module module) doc (assoc :decl/doc doc))))
    (doseq [[kind n _ prio] attrs]
      (ent! n #(cond-> (update % :decl/attr (fnil conj #{}) kind)
                 (and (= kind "simp") prio) (assoc :decl/simp-prio prio))))
    (doseq [[_ insts] instances {:keys [name priority]} insts]
      (ent! (str name) #(cond-> (update % :decl/attr (fnil conj #{}) "instance")
                          priority (assoc :decl/instance-prio priority))))
    (vec (.values by-name))))

(defn- ref-datoms
  "[:db/add e a v] for every ref, resolved through `eid-of`; refs to names outside the
   catalogue (auxiliary constants filtered out at keying) are dropped."
  [{:keys [facts instances]} eid-of]
  ;; `distinct` per source: the dump declares its datom count and `import-db` verifies it, so a
  ;; duplicate ref (an instance registered twice, a name reached twice) must not reach the dump.
  (concat
   (for [f facts, [attr names] [[:decl/mentions (:mentions f)] [:decl/depends-on (:depends-on f)]]
         :let [e (eid-of (:name f))] :when e
         n (distinct names) :let [v (eid-of n)] :when v]
     [:db/add e attr v])
   (distinct
    (for [[cls insts] instances {:keys [name]} insts
          :let [e (eid-of (str name)) c (eid-of (str cls))] :when (and e c)]
      [:db/add e :decl/instance-of c]))))

(defn- facts-chunks
  "[i (fn [] facts-of-chunk-i)] for the store's facts chunk blobs."
  [store-map branch]
  (let [read-derived (requiring-resolve 'ansatz.export.storage/read-derived)
        st (:store store-map)
        n (or (read-derived st branch :facts-chunks) 0)]
    (mapv (fn [i] [i (fn [] (read-derived st branch [:facts i]))]) (range n))))

;; ---- the bulk build: ONE index build from a dump, not thousands of commits ----

(defn- write-chunk!
  "Write `records` to `file` as a CBOR sequence exactly as datahike's exporter does — one
   `encode-record` per record, no delimiter — folding the same bytes into the chunk SHA-256
   and the semantic-digest accumulator. Returns [chunk-descriptor dacc']."
  [^java.io.File file name records dacc]
  (let [md (dig/sha256-accumulator)]
    (with-open [out (io/output-stream file)]
      (loop [rs (seq records) n 0 raw 0 da dacc]
        (if rs
          (let [^bytes bs (mcbor/encode-record (first rs))]
            (.write out bs)
            (dig/sha256-update! md bs)
            (recur (next rs) (inc n) (+ raw (alength bs)) (dig/add-record da bs)))
          [{:file name :count n :bytes raw :raw-bytes raw :sha256 (dig/sha256-finalize md)} da])))))

(defn- scalar-records
  "[e a v tx true] for an entity map, one record per value of a many-valued attribute."
  [eid ent tx]
  (for [[a v] ent, v (if (set? v) v [v])] [eid a v tx true]))

(defn build!
  "Build the catalogue as datahike's index-build import: write a DUMP — the schema and system
   datoms from a schema-only export, then our records appended as chunks with the manifest
   continued (counts, per-chunk SHA-256, semantic digest) — and `import-db` it with
   `:build-indexes? true`, which builds all six index trees from three external sorts in ONE
   commit. Transacting the same datoms in batches — the first cut — rewrote most of the
   copy-on-write trees at every commit: 15 GB of superseded nodes for Mathlib, reachable
   through the commit graph until a GC with a cutoff pruned them. One build, one commit.
   The disc-tree secondary indices cannot be part of an index build, so they are declared
   AFTER it — datahike backfills them from AEVT in the background — and this waits until both
   report `:ready`. Same inputs as `build!`. Returns counts."
  [store-path {:keys [branch log store-map reuse-dump?] :or {branch "main" log println} :as data}]
  (let [t0 (System/nanoTime)
        open-store (requiring-resolve 'ansatz.export.storage/open-store)
        read-derived (requiring-resolve 'ansatz.export.storage/read-derived)
        sm (or store-map (open-store store-path))
        st (:store sm)
        data (cond-> data
               (not (contains? data :recall-keys)) (assoc :recall-keys (read-derived st branch :recall-keys))
               (not (contains? data :simp-keys)) (assoc :simp-keys (read-derived st branch :simp-keys))
               (not (contains? data :attrs)) (assoc :attrs (read-derived st branch :attrs))
               (not (contains? data :instances)) (assoc :instances (read-derived st branch :instances)))
        chunks (facts-chunks sm branch)
        facts (fn [] (mapcat (fn [[_ f]] (f)) chunks))
        dump (io/file store-path "catalogue-dump")
        scratch-dir (io/file store-path "catalogue-scratch")
        base-cfg (dissoc (config store-path) :store)]
    ;; 1. schema-only export: manifest + system/schema datoms, by datahike itself
    ;;    (`:reuse-dump? true` keeps a dump a previous run wrote and skips to the import)
    (doseq [d [scratch-dir]] (when (.exists d) (run! #(.delete ^java.io.File %) (reverse (file-seq d)))))
    (when-not (and reuse-dump? (.exists (io/file dump "manifest.edn")))
     (when (.exists dump) (run! #(.delete ^java.io.File %) (reverse (file-seq dump))))
     (let [scfg (assoc base-cfg :store {:backend :file :path (.getPath scratch-dir) :id (java.util.UUID/randomUUID)})]
      (d/create-database scfg)
      (let [conn (d/connect scfg)]
        (try (d/transact conn schema-tx)
             (migrate/export-db @conn (.getPath dump) {:compression :none})
             (finally (d/release conn))))
      (d/delete-database scfg)))
    (let [manifest (edn/read-string (slurp (io/file dump "manifest.edn")))
          sys-chunk (first (:chunks manifest))
          sys-bytes (java.nio.file.Files/readAllBytes (.toPath (io/file dump (:file sys-chunk))))
          dacc (reduce dig/add-record (dig/accumulator)
                       (map mcbor/encode-record (mcbor/decode-records-from sys-bytes)))
          base-eid (long (inc (get-in manifest [:stats :max-eid])))
          tx (long (inc (get-in manifest [:stats :max-tx])))
          reused? (and reuse-dump? (> (count (:chunks manifest)) 1))
          ;; 2. our records: scalars (entities in declaration order → contiguous ids), then refs
          ents (if reused? [] (scalar-entities (assoc data :facts (facts))))
          eid-of (let [m (java.util.HashMap.)]
                   (doseq [[i e] (map-indexed vector ents)] (.put m (:decl/name e) (+ base-eid (long i))))
                   (fn [n] (.get m n)))
          records (concat (mapcat (fn [i e] (scalar-records (+ base-eid (long i)) e tx)) (range) ents)
                          (map (fn [[_ e a v]] [e a v tx true])
                               (ref-datoms (assoc data :facts (facts)) eid-of)))
          ;; 3. chunks of 100k, manifest continued
          [descs dacc n]
          (loop [rs (when-not reused? (seq records)) i (inc (count (:chunks manifest))) descs [] da dacc n 0]
            (if rs
              (let [name (format "datoms-%06d.cbor" i)
                    [desc da'] (write-chunk! (io/file dump name) name (take 100000 rs) da)]
                (log "    dump chunk" name (:count desc) "records")
                (recur (seq (drop 100000 rs)) (inc i) (conj descs desc) da' (+ n (long (:count desc)))))
              [descs da n]))
          total (if reused? (get-in manifest [:stats :datom-count]) (+ (long (:count sys-chunk)) n))
          manifest' (if reused?
                      manifest
                      (-> manifest
                          (update :chunks into descs)
                          (assoc :semantic-digest (dig/finalize dacc))
                          (update :stats assoc :datom-count total :source-datom-count total
                                  :max-eid (+ base-eid (count ents) -1) :max-tx tx)))]
      (when-not reused? (spit (io/file dump "manifest.edn") (pr-str manifest')))
      (log (if reused? "    dump reused:" "    dump written:") total "datoms in" (count (:chunks manifest')) "chunks")
      ;; 4. one index build
      (let [cfg (config store-path)
            cat-dir (catalogue-dir store-path)]
        (when (d/database-exists? cfg) (d/delete-database cfg))
        ;; a killed build leaves a directory konserve calls a store and datahike does not call a
        ;; database; the catalogue is derived and ours, so clear it
        (when (.exists cat-dir) (run! #(.delete ^java.io.File %) (reverse (file-seq cat-dir))))
        (d/create-database cfg)
        (let [conn (d/connect cfg)]
          (try
            (let [r (migrate/import-db conn (.getPath dump) {:build-indexes? true :eids :preserve :verify? true})]
              (log "    index build:" (pr-str (select-keys r [:datoms :elapsed-ms :ok?]))))
            ;; 5. the disc-tree indices, backfilled from AEVT
            (d/transact conn index-tx)
            (loop [waited 0]
              (let [status (mapv #(get-in @conn [:schema % :db.secondary/status]) [:idx/dt :idx/simp])]
                (cond (every? #{:ready} status) (log "    secondary indices ready after" waited "s")
                      (> waited 7200) (throw (ex-info "secondary index backfill did not finish" {:status status}))
                      :else (do (Thread/sleep 5000) (recur (+ waited 5))))))
            (finally (d/release conn)))))
      (run! #(.delete ^java.io.File %) (reverse (file-seq dump)))
      {:entities (if reused? (- (get-in manifest [:stats :max-eid]) base-eid -1) (count ents)) :datoms total :dt-keys (count (:recall-keys data)) :simp-keys (count (:simp-keys data))
       :facts-chunks (count chunks) :elapsed-ms (quot (- (System/nanoTime) t0) 1000000)})))

(defn exists? [store-path] (d/database-exists? (config store-path)))

(defn connect
  "A connection to the store's catalogue, or nil when it has none. The catalogue's `:id` is
   derived from the path it was BUILT at; a store that has since been renamed, moved or
   downloaded elsewhere keeps its catalogue, so on datahike's identity mismatch (which only
   compares ids — the path already names the one catalogue a store has) we reconnect with
   the id the catalogue carries."
  [store-path]
  (when (exists? store-path)
    (let [cfg (config store-path)]
      (try (d/connect cfg)
           (catch clojure.lang.ExceptionInfo e
             (if-let [stored-id (and (= :store-identity-mismatch (:type (ex-data e)))
                                     (:stored-id (ex-data e)))]
               (d/connect (assoc-in cfg [:store :id] stored-id))
               (throw e)))))))

(defn- names-of [db eids]
  (when (seq eids)
    (map first (d/q '[:find ?n :in $ [?d ...] :where [?d :decl/name ?n]] db eids))))

(defn- search [db idx key-path]
  (dti/search-eids (get (:secondary-indices db) idx) key-path))

(defn recall-names
  "Declarations whose CONCLUSION structurally matches `key-path` (a query key from
   ansatz.recall/query-key or its EDN string), through the persisted `:idx/dt`."
  [db key-path] (names-of db (search db :idx/dt key-path)))

(defn simp-lemma-names
  "@[simp] lemmas whose LHS structurally matches `key-path`, through the persisted `:idx/simp`."
  [db key-path] (names-of db (search db :idx/simp key-path)))

;; ---- the current store's catalogue, connected on first demand ----

(defonce ^:private current (atom nil))   ; {:store-path p :conn c} — only a LIVE connection

(defn current-db
  "The current store's catalogue DB (connected on first use, cached), or nil when the store at
   `store-path` has none. Absence is never cached: a catalogue built later in the session is
   picked up on the next call."
  [store-path]
  (let [{:keys [conn] :as cur} @current]
    (if (and cur conn (= (:store-path cur) store-path))
      @conn
      (do (when conn (d/release conn))
          (reset! current nil)
          (when-let [c (connect store-path)]
            (reset! current {:store-path store-path :conn c})
            @c)))))
