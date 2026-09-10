(ns ansatz.recall
  "Persistent RECALL projection: the disc-tree keying of a store's declaration
   CONCLUSIONS, computed once by the importer (ansatz.import) into the store's derived
   `:recall-keys` blob — each key forces the decl's type DAG out of PSS, ~1-2 h for Mathlib
   serially, minutes in parallel — and served at query time from the store's catalogue
   (ansatz.catalogue, the durable disc-tree index) or, without one, from an in-memory trie
   built on first use. A dependency-light leaf (dt + kernel only)."
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [clojure.string :as str]
            [clojure.edn :as edn])
  (:import [ansatz.kernel ConstantInfo Name]))

(defn- edn-safe-keys
  "Make a disc-tree key-path EDN-round-trippable: a :const key's `:name` is a
   kernel Name → stringify it. Applied to BOTH stored and query keys so they
   compare consistently in the trie."
  [keys]
  (mapv (fn [k] (if (instance? Name (:name k)) (update k :name nm/->string) k)) keys))

(defn decl-key
  "Disc-tree key for a declaration TYPE: peel the ∀-telescope (binders → star
   mvars, so a lemma `∀ n, 0 ≤ n` keys as `0 ≤ *`), then key the conclusion.
   Returns an edn-safe key-path (Name → string)."
  [ty]
  (loop [t ty, i 0]
    (if (e/forall? t)
      (recur (e/instantiate1 (e/forall-body t) (e/mvar (+ 800000 i))) (inc i))
      (edn-safe-keys (dt/expr->keys t)))))

(defn query-key
  "Query key-path for a goal type (holes/mvars → star)."
  [goal] (edn-safe-keys (dt/expr->keys goal)))

;; ---- G: skip auto-generated decls (equation lemmas, recursors, match eqns,
;;      internal proofs) — not useful recall targets, and their huge keys blow
;;      up the trie. Cuts the corpus ~3-4x and improves recall precision. ----
(def ^:private auto-gen-substrings
  [".eq_" "._eq_" ".eq_def" ".rec" ".recAux" ".brecOn" ".below" ".ibelow"
   ".casesOn" ".noConfusion" ".match_" ".fun_" "._proof_" ".proof_" "._impl"
   "._unary" ".ind" ".sizeOf" ".injEq" ".mk.inj" "._simp_" ".rawCast" "_private."])

(defn useful?
  "A declaration worth indexing for recall (excludes compiler-generated aux)."
  [name-str]
  (not (some #(str/includes? name-str %) auto-gen-substrings)))

(defn decl-keys
  "The recall entries `[name key-str]` for the USEFUL declarations in `decl-names` (resolved
   via `resolve-fn : name-str → ConstantInfo|nil`; a nil or a failing keying is skipped, as is
   a key longer than `max-key-len`). The one-time, type-forcing keying pass the importer runs
   — in parallel, one resolver per worker."
  [decl-names resolve-fn & {:keys [max-key-len] :or {max-key-len 120}}]
  (into []
        (keep (fn [nam]
                (when (useful? nam)
                  (let [ci (try (resolve-fn nam) (catch Throwable _ nil))
                        ks (when ci (try (decl-key (.type ^ConstantInfo ci)) (catch Throwable _ nil)))]
                    (when (and ks (< (count ks) max-key-len))
                      [nam (pr-str ks)])))))
        decl-names))

(defn build-discr-trie
  "The recall disc-tree from `[name key-str]` entries — trie-insert only; the expensive keying
   was done at import."
  [entries]
  (reduce (fn [trie [nam k]] (dt/trie-insert trie (edn/read-string k) nam))
          dt/empty-trie entries))

(defonce store-path
  ^{:doc "Path of the current store (set by ansatz.core/init!), or nil. When the store carries a
          catalogue (`<store>/catalogue`, ansatz.catalogue on the :datahike alias) recall is
          answered from its persisted disc-tree index instead of the in-memory trie."}
  (atom nil))

(defn- current-store []
  @(deref (requiring-resolve 'ansatz.state/ansatz-store)))

(defn ensure-discr-trie!
  "The recall trie for the current store, built on FIRST use from its derived `:recall-keys`
   blob (~50 s for Mathlib — the catalogue is the fast path; this is the fallback) and cached
   in ansatz.state/ansatz-discr-trie; nil for the bundled tier or a store without keys."
  []
  (or @(deref (requiring-resolve 'ansatz.state/ansatz-discr-trie))
      (when-let [{:keys [store-map branch]} (current-store)]
        (let [read-derived (requiring-resolve 'ansatz.export.storage/read-derived)
              trie (when-let [entries (read-derived (:store store-map) branch :recall-keys)]
                     (build-discr-trie entries))]
          (reset! (deref (requiring-resolve 'ansatz.state/ansatz-discr-trie)) trie)
          trie))))

;; ---- recall: durable catalogue first, in-memory trie as the fallback ----

(defn- catalogue-db
  "The current store's catalogue DB, or nil: no store, no catalogue, or datahike not on the
   classpath (ansatz.catalogue lives under the :datahike alias)."
  []
  (when-let [p @store-path]
    (try ((requiring-resolve 'ansatz.catalogue/current-db) p)
         (catch java.io.FileNotFoundException _ nil))))

(defn recall-names
  "Declarations whose CONCLUSION structurally matches `goal-type` (holes → stars), deduped.
   Served from the store's persisted catalogue index when it has one (a ~130 ms connect on
   first use), else from the in-memory trie built on first use from the store's recall keys;
   nil when the current env has neither."
  [goal-type]
  (let [k (query-key goal-type)]
    (if-let [db (catalogue-db)]
      ((requiring-resolve 'ansatz.catalogue/recall-names) db k)
      (when-let [trie (ensure-discr-trie!)]
        (distinct (dt/trie-match trie k))))))
