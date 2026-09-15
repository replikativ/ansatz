(ns ansatz.import
  "ONE importer: a Lean export in, a COMPLETE store out.

   A store is more than its blobs. Everything a session needs — the inherited attributes, the
   instance registry, the matcher corpus, the recall keys, the @[simp] LHS keys and the trie
   over them, the catalogue — used to be six scripts, three of them undocumented, run by hand
   after the setup script; a store missing any of them degraded silently (no simp keys: the
   inherited @[simp] set goes back to hydrating ~91k lemmas per call). `import!` produces all of
   it in one run and writes the manifest LAST, so a store is complete exactly when the manifest
   exists, and `init!` refuses one without it.

   INPUTS (from a Lean toolchain — CI is the natural place; see scripts/setup-mathlib.sh):
     :ndjson      the lean4export NDJSON of the library
     :attrs       scripts/dump_attrs.lean output (.ndjson or .ndjson.gz)         — optional
     :instances   scripts/dump_instances.lean TSV                                  — optional
     :modules     scripts/dump_modules.lean output: module + docstring per name    — optional
     :provenance  {:lean/toolchain :library/rev :lean4export/rev ...} recorded in the manifest

   LAYOUT written:
     <store>/manifest.edn     format, provenance, artifact inventory  (last)
     <store>/blobs/           konserve: PSS nodes (content-addressed CBOR), branch metadata,
                              decl-order chunks, and the derived state under [:derived <branch> k]
     <store>/catalogue/       datahike, when ansatz.catalogue (the :datahike alias) is loadable
     <store>/inputs/          the small inputs as received, for regeneration without Lean

   The keying passes resolve every declaration's type out of the store (hours for Mathlib
   serially); they run on `:parallelism` workers, each with its OWN resolver — the resolver
   caches are not thread-safe."
  (:require [ansatz.export.storage :as storage]
            [ansatz.store :as store]
            [ansatz.attrs :as attrs]
            [ansatz.matchers :as matchers]
            [ansatz.recall :as recall]
            [ansatz.simp-index :as si]
            [ansatz.export.facts :as facts]
            [ansatz.tactic.instance :as instance]
            [ansatz.kernel.env :as env]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.util.concurrent Executors ExecutorService Future]))

(defn- log! [lw & args]
  (let [msg (apply str (interpose " " args))]
    (println msg)
    (when lw (.write ^java.io.Writer lw (str msg "\n")) (.flush ^java.io.Writer lw))))

(defn- elapsed-s [t0] (quot (- (System/nanoTime) t0) 1000000000))

(defn- parallel-keying
  "Split `names` into `parallelism` chunks; each worker keys its chunk with its own resolver
   (`make-resolver` → resolve-fn) through `key-fn : (resolve-fn names) → entries`. Results in
   input order."
  [names parallelism make-resolver key-fn]
  (let [n (max 1 (long parallelism))
        chunks (partition-all (max 1 (quot (+ (count names) (dec n)) n)) names)
        ^ExecutorService pool (Executors/newFixedThreadPool n)]
    (try
      (let [futures (mapv (fn [chunk] (.submit pool ^Callable (fn [] (key-fn (make-resolver) (vec chunk))))) chunks)]
        (into [] (mapcat (fn [^Future f] (.get f))) futures))
      (finally (.shutdown pool)))))

(defn- facts-pass!
  "Compute and PERSIST the facts of `decl-order` in chunks of 50k — each chunk keyed in parallel,
   written as `[:derived branch [:facts i]]` before the next begins — so memory holds one chunk,
   not the library (648k fact maps with their mention/dependency lists is what an 8 GB heap
   could not hold). Returns {:chunks n :facts n :mentions n :depends-on n}."
  [sm kstore branch decl-order parallelism log]
  (let [name-cache (java.util.concurrent.ConcurrentHashMap.)
        chunks (partition-all 50000 decl-order)
        totals (atom {:chunks 0 :facts 0 :mentions 0 :depends-on 0})]
    (doseq [[i chunk] (map-indexed vector chunks)]
      (let [fs (parallel-keying (vec chunk) parallelism (constantly nil)
                                (fn [_ names] (facts/facts-for sm branch name-cache names)))]
        (storage/write-derived! kstore branch [:facts i] fs)
        (swap! totals (fn [t] (-> t (update :chunks inc) (update :facts + (count fs))
                                  (update :mentions + (reduce + (map (comp count :mentions) fs)))
                                  (update :depends-on + (reduce + (map (comp count :depends-on) fs))))))
        (log "    facts chunk" i (count fs) "declarations")))
    (storage/write-derived! kstore branch :facts-chunks (:chunks @totals))
    @totals))

(defn- copy-input! [src dst-dir]
  (when src
    (let [f (io/file src)]
      (when (.exists f)
        (.mkdirs (io/file dst-dir))
        (io/copy f (io/file dst-dir (.getName f)))
        (.getName f)))))

(defn import!
  "Import the Lean export at `:ndjson` into the store at `store-path` (created; refuses a
   directory that already holds a manifest). Returns the manifest.

   Options: :branch (default \"main\"), :attrs, :instances, :provenance, :parallelism (default:
   available processors), :log-file, :verbose?, :max-count (import only the first N
   declarations — tests)."
  [store-path {:keys [ndjson attrs instances modules branch provenance parallelism log-file verbose? max-count]
               :or {branch "main" verbose? true
                    parallelism (.availableProcessors (Runtime/getRuntime))}}]
  (when (.exists (store/manifest-file store-path))
    (throw (ex-info "store already exists (has a manifest); delete it to re-import" {:store store-path})))
  (when-not (and ndjson (.exists (io/file ndjson)))
    (throw (ex-info "no such export" {:ndjson ndjson})))
  (.mkdirs (io/file store-path))
  (let [t0 (System/nanoTime)
        log-file (or log-file (str store-path "/import.log"))
        lw (java.io.FileWriter. ^String log-file false)
        sm (storage/open-store store-path {:sync-blob? false})
        kstore (:store sm)]
    (try
      (log! lw "import!" ndjson "->" store-path "branch" branch "parallelism" parallelism)
      ;; 1. the blobs: env/exprs/names/levels trees + branch metadata + decl-order
      (let [branch-meta (storage/import-ndjson-streaming! sm ndjson branch
                                                          :verbose? verbose? :max-count max-count
                                                          :log-file (str store-path "/import-blobs.log"))
            _ (log! lw "  blobs done:" (:env-count branch-meta) "declarations," (elapsed-s t0) "s")
            present? (storage/contains-name-checker sm branch)
            decl-order (storage/load-decl-order sm branch)
            ;; 2. attrs: filter the corpus to this store's names once, persist the tuples
            attr-tuples (when attrs
                          (let [all (attrs/read-attr-file attrs)
                                kept (filterv (fn [[_ n _ _]] (present? n)) all)]
                            (log! lw "  attrs:" (count kept) "of" (count all) "kept")
                            kept))
            simp-names (into #{} (comp (filter (fn [[k _ _ _]] (contains? #{"simp" "csimp"} k)))
                                       (map second))
                             attr-tuples)
            _ (when attr-tuples (storage/write-derived! kstore branch :attrs attr-tuples))
            ;; 3. instances: the TSV registry, else name-based discovery over the env
            inst-index (if (and instances (.exists (io/file instances)))
                         (instance/load-instance-tsv instances)
                         (instance/build-instance-index (storage/load-env sm branch :value-policy :defs-only)))
            _ (storage/write-derived! kstore branch :instances inst-index)
            _ (log! lw "  instances:" (count inst-index) "classes")
            ;; 4. matchers: the bundled Init corpus, intersected
            matcher-map (into {} (filter (fn [[n _]] (present? n))) (matchers/bundled-matchers))
            _ (storage/write-derived! kstore branch :matchers matcher-map)
            _ (log! lw "  matchers:" (count matcher-map))
            ;; 5. recall keys: every useful declaration's conclusion, in parallel
            t-recall (System/nanoTime)
            recall-entries (parallel-keying decl-order parallelism
                                            #(storage/branch-resolver sm branch :value-policy :defs-only)
                                            (fn [resolve-fn names] (recall/decl-keys names resolve-fn)))
            _ (storage/write-derived! kstore branch :recall-keys recall-entries)
            _ (log! lw "  recall keys:" (count recall-entries) "in" (elapsed-s t-recall) "s")
            ;; 6. simp keys + the trie over them (lemma rfl-flags read the PROOF: keep values)
            t-simp (System/nanoTime)
            simp-env (storage/load-env sm branch :value-policy :defs-only :keep-value? simp-names)
            simp-entries (parallel-keying (vec (sort simp-names)) parallelism
                                          #(storage/branch-resolver sm branch :value-policy :defs-only
                                                                    :keep-value? simp-names)
                                          (fn [resolve-fn names] (si/lemma-keys names simp-env resolve-fn)))
            _ (storage/write-derived! kstore branch :simp-keys simp-entries)
            _ (storage/write-derived! kstore branch :simp-trie (si/build-simp-trie simp-entries))
            _ (log! lw "  simp keys:" (count simp-entries) "for" (count simp-names) "lemmas in" (elapsed-s t-simp) "s")
            ;; 7. facts: kind/universes/binders/head + MENTIONS (statement) + DEPENDS-ON (value),
            ;;    by a raw walk of the expression records — no Expr objects (ansatz.export.facts);
            ;;    streamed to the store chunk by chunk
            t-facts (System/nanoTime)
            facts-stats (facts-pass! sm kstore branch decl-order parallelism (fn [& a] (apply log! lw a)))
            _ (log! lw "  facts:" (:facts facts-stats) "declarations," (:mentions facts-stats) "mentions,"
                    (:depends-on facts-stats) "dependencies in" (elapsed-s t-facts) "s")
            ;; the module/doc dump (scripts/dump_modules.lean), when given
            module-facts (when modules (facts/read-modules-file modules))
            _ (when modules (log! lw "  modules:" (count module-facts) "declarations with module/doc"))
            ;; 8. the catalogue, when datahike is on the classpath
            catalogue (try (let [build! (requiring-resolve 'ansatz.catalogue/build!)]
                             (storage/flush-writes! (:storage sm))
                             (let [r (build! store-path {:branch branch
                                                         :recall-keys recall-entries
                                                         :simp-keys simp-entries
                                                         :store-map sm            ; facts read lazily from its chunks
                                                         :modules module-facts
                                                         :attrs attr-tuples
                                                         :instances inst-index
                                                         :log (fn [& args] (apply log! lw args))})]
                               (log! lw "  catalogue:" (pr-str r))
                               r))
                           (catch java.io.FileNotFoundException _
                             (log! lw "  catalogue: skipped (ansatz.catalogue not on the classpath)")
                             nil))
            ;; 9. inputs kept alongside, then the manifest LAST
            inputs (vec (keep #(copy-input! % (io/file store-path "inputs")) [attrs instances modules]))
            manifest {:store/format store/store-format
                      :ansatz/version (or (System/getProperty "ansatz.version") "dev")
                      :branch branch
                      :created (java.util.Date.)
                      :provenance provenance
                      :inputs inputs
                      :artifacts {:declarations (:env-count branch-meta)
                                  :expressions (:exprs-count branch-meta)
                                  :names (:names-count branch-meta)
                                  :levels (:levels-count branch-meta)
                                  :attrs (count attr-tuples)
                                  :instances (count inst-index)
                                  :matchers (count matcher-map)
                                  :recall-keys (count recall-entries)
                                  :simp-keys (count simp-entries)
                                  :facts (:facts facts-stats)
                                  :modules (count module-facts)
                                  :catalogue (boolean catalogue)}
                      :elapsed-s (elapsed-s t0)}]
        (storage/close-store sm)
        (store/write-manifest! store-path manifest)
        (log! lw "import! DONE in" (elapsed-s t0) "s")
        manifest)
      (finally (.close lw)))))

(defn rebuild-instances!
  "Replace an existing format-1 store's derived `:instances` blob from a fresh
   scripts/dump_instances.lean TSV (module order, real priorities) — for a store whose registry
   was written by the old inline emitter (hash order, every priority 100). Leaves the blobs
   alone; keeps the TSV under <store>/inputs/. Returns the class count."
  [store-path tsv & {:keys [branch] :or {branch "main"}}]
  (store/check-format! store-path)
  (let [sm (storage/open-store store-path {:sync-blob? false})
        idx (instance/load-instance-tsv tsv)]
    (storage/write-derived! (:store sm) branch :instances idx)
    (copy-input! tsv (io/file store-path "inputs"))
    (count idx)))

(defn rebuild-catalogue!
  "Recompute the FACTS (ansatz.export.facts) and the catalogue of an existing format-1 store,
   optionally with a module/doc dump — for a store imported before facts existed, or a new
   dump. Leaves the blobs alone. Returns the catalogue counts."
  [store-path {:keys [branch modules parallelism log-file refacts? reuse-dump?]
               :or {branch "main" parallelism (.availableProcessors (Runtime/getRuntime))}}]
  (store/check-format! store-path)
  (let [t0 (System/nanoTime)
        lw (java.io.FileWriter. ^String (or log-file (str store-path "/rebuild-catalogue.log")) false)
        sm (storage/open-store store-path {:sync-blob? false})
        kstore (:store sm)]
    (try
      (let [decl-order (storage/load-decl-order sm branch)
            ;; facts persisted by an earlier run are reused (`:refacts? true` recomputes)
            facts-stats (if (and (storage/read-derived kstore branch :facts-chunks) (not refacts?))
                          (let [n (reduce + (map #(count (storage/read-derived kstore branch [:facts %]))
                                                 (range (storage/read-derived kstore branch :facts-chunks))))]
                            (log! lw "  facts: reusing the store's" n)
                            {:facts n})
                          (facts-pass! sm kstore branch decl-order parallelism (fn [& a] (apply log! lw a))))
            _ (log! lw "  facts:" (pr-str facts-stats) "in" (elapsed-s t0) "s")
            module-facts (when modules (facts/read-modules-file modules))
            _ (copy-input! modules (io/file store-path "inputs"))
            build! (requiring-resolve 'ansatz.catalogue/build!)
            r (build! store-path {:branch branch
                                  :recall-keys (storage/read-derived kstore branch :recall-keys)
                                  :simp-keys (storage/read-derived kstore branch :simp-keys)
                                  :store-map sm
                                  :reuse-dump? reuse-dump?
                                  :modules module-facts
                                  :attrs (storage/read-derived kstore branch :attrs)
                                  :instances (storage/read-derived kstore branch :instances)
                                  :log (fn [& args] (apply log! lw args))})]
        (storage/close-store sm)
        (store/write-manifest! store-path
                               (-> (store/read-manifest store-path)
                                   (assoc-in [:artifacts :facts] (:facts facts-stats))
                                   (assoc-in [:artifacts :modules] (count module-facts))
                                   (assoc-in [:artifacts :catalogue] true)))
        (log! lw "rebuild-catalogue! DONE in" (elapsed-s t0) "s" (pr-str r))
        r)
      (finally (.close lw)))))

(defn -main
  "clj -M -m ansatz.import <store-path> <ndjson> [branch] [attrs] [instances] [modules] [k=v provenance...]
   (`-` for an absent optional file)"
  [& [store-path ndjson branch attrs instances modules & kvs]]
  (when-not (and store-path ndjson)
    (println "usage: ansatz.import <store-path> <ndjson> [branch] [attrs] [instances] [modules] [key=value ...]")
    (System/exit 2))
  (let [prov (into {} (map (fn [kv] (let [[k v] (str/split kv #"=" 2)] [(keyword k) v])) kvs))]
    (prn (import! store-path {:ndjson ndjson :branch (or branch "main")
                              :attrs (when (and attrs (not= attrs "-")) attrs)
                              :instances (when (and instances (not= instances "-")) instances)
                              :modules (when (and modules (not= modules "-")) modules)
                              :provenance prov}))
    (shutdown-agents)))
