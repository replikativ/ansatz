(ns ansatz.catalogue
  "The store CATALOGUE: a datahike DB at `<store>/catalogue` holding the facts a prover reads
   about declarations — today `:decl/name`, the conclusion disc-tree key (`:decl/dt-key`) and
   the @[simp] LHS keys (`:decl/simp-key`, many) — with the DURABLE disc-tree secondary index
   (ansatz.index.discr) as two instances: `:idx/dt` for recall, `:idx/simp` for simp. Built
   ONCE by the importer (ansatz.import) from the recall and simp keys in a single transaction;
   afterwards a fresh process `connect`s in ~130 ms and answers structural queries from
   persisted chunks — nothing is rebuilt per session. The in-memory tries (ansatz.recall,
   ansatz.simp-index) remain the fallback when a store has no catalogue.

   Lives under src-datahike (the `:datahike` alias): ansatz proper never depends on datahike;
   ansatz.recall reaches this namespace by `requiring-resolve` and degrades when absent."
  (:require [datahike.api :as d]
            [ansatz.index.discr :as dti]
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
  [{:db/ident :decl/name :db/valueType :db.type/string :db/cardinality :db.cardinality/one
    :db/unique :db.unique/identity}
   {:db/ident :decl/dt-key :db/valueType :db.type/string :db/cardinality :db.cardinality/one}
   {:db/ident :decl/simp-key :db/valueType :db.type/string :db/cardinality :db.cardinality/many}])

(def index-tx
  [{:db/ident :idx/dt :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/dt-key]}
   {:db/ident :idx/simp :db.secondary/type :ansatz.index/discr-tree :db.secondary/attrs [:decl/simp-key]}])

(defn entities
  "Merge the recall and simp key entries (`[name key-str]`) into one entity map per name."
  [recall-keys simp-keys]
  (let [by-name (reduce (fn [m [n k]] (assoc m n {:decl/name n :decl/dt-key k})) {} recall-keys)
        by-name (reduce (fn [m [n k]] (update m n (fn [e] (-> (or e {:decl/name n})
                                                            (update :decl/simp-key (fnil conj #{}) k)))))
                        by-name simp-keys)]
    (vec (vals by-name))))

(defn build!
  "Build (or REBUILD) the catalogue of the store at `store-path` from its recall and simp key
   entries in ONE transaction, so the durable index is flushed once (no stale chunk versions).
   Takes the entries as data — `{:recall-keys [[name key] …] :simp-keys [[name key] …]}` — as
   the importer passes them; with `:branch` alone, reads the store's derived blobs.
   Returns {:entities n :dt-keys n :simp-keys n :elapsed-ms n}."
  [store-path {:keys [branch recall-keys simp-keys] :or {branch "main"}}]
  (let [cfg (config store-path)
        t0 (System/nanoTime)
        [recall-keys simp-keys]
        (if (or recall-keys simp-keys)
          [recall-keys simp-keys]
          (let [open-store (requiring-resolve 'ansatz.export.storage/open-store)
                read-derived (requiring-resolve 'ansatz.export.storage/read-derived)
                sm (open-store store-path)]
            [(read-derived (:store sm) branch :recall-keys)
             (read-derived (:store sm) branch :simp-keys)]))
        ents (entities recall-keys simp-keys)]
    (when (d/database-exists? cfg) (d/delete-database cfg))
    (d/create-database cfg)
    (let [conn (d/connect cfg)]
      (try
        (d/transact conn schema-tx)
        (d/transact conn index-tx)
        (d/transact conn {:tx-data ents})
        {:entities (count ents) :dt-keys (count recall-keys) :simp-keys (count simp-keys)
         :elapsed-ms (quot (- (System/nanoTime) t0) 1000000)}
        (finally (d/release conn))))))

(defn exists? [store-path] (d/database-exists? (config store-path)))

(defn connect
  "A connection to the store's catalogue, or nil when it has none."
  [store-path]
  (when (exists? store-path) (d/connect (config store-path))))

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
