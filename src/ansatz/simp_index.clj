(ns ansatz.simp-index
  "Persistent @[simp] index: the disc-tree LHS keying of a store's @[simp] lemma corpus, computed
   once by the importer into the store's derived `:simp-keys`/`:simp-trie` blobs and loaded on
   first demand.

   At Mathlib scale the inherited @[simp] set is ~91k names, and without this `simp` resolved
   (hydrated from PSS), extracted and keyed ALL of them — plus an equation-theorem probe and an
   unfold probe per name — on EVERY call, which made a full-set simp unusable there. This is
   ansatz.recall's pattern applied to simp: dump `name → LHS-key` offline, load a compact
   `key → name` trie on first use, and at rewrite time look candidate NAMES up by the goal
   subterm's key, resolving+extracting the rule for only the handful that structurally match
   (cached for the session). The eager per-call path stays for the hand-curated core, user
   lemmas, hypotheses and equation theorems; on stores without the artifact (the bundled Init
   tiers) everything stays eager as before.

   A dependency-light leaf: simp's private CI → rule extractor is reached through its var so
   ansatz.tactic.simp can require this namespace without a cycle; the disc-tree keying is
   `dt/expr->keys`, so stored keys match what `build-lemma-index`/`lookup-simp-tree` produce."
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.state :as state]
            [ansatz.simp-sources :as sources]
            [clojure.edn :as edn])
  (:import [ansatz.kernel Name ConstantInfo]))

(def extension-key
  "The Env extension naming the store whose derived simp index serves this env:
   `{:store-path p :branch b}`, set by ansatz.core/init!. It rides on the immutable Env like
   the attrs extensions do, so an env built any other way (replay, a test fixture's `reset!`)
   has NO index and stays on the eager path — the index can never leak from one store's env
   into another's."
  sources/index-key)

(defn index-source
  "The `{:store-path :branch}` recorded on `env`, or nil."
  [env] (env/get-extension env extension-key nil))

(def ^:private captured-index-key sources/captured-key)
(def eager-overlay-key
  "Explicit local and bounded supplement lemma names served beside a base trie."
  sources/eager-key)

(defn eager-lemma-names
  "Use inherited names eagerly without a trie, and only explicit local/role additions
   beside a persistent base trie. Never scan/rebuild a store corpus for an overlay."
  [env trie]
  (env/get-extension env (if trie eager-overlay-key :simp-lemmas) #{}))

(defn with-index-source
  "`env` with its simp-index source set (nil clears it)."
  [env source]
  (-> env
      (env/update-extension extension-key nil (constantly source))
      (env/with-extension captured-index-key nil)))

(defn with-captured-index
  "Retain the immutable derived trie observed during init, bound to the actual
   external Env view. Later branch/global-store changes cannot replace it. This
   records an observed value; it does not establish CI/index co-generation."
  [env source trie]
  (when-not (and (map? source) (map? trie))
    (throw (ex-info "Captured simp index requires a source and immutable trie" {})))
  (let [view (with-index-source env source)]
    (env/with-extension view captured-index-key {:trie trie :view view})))

(defonce ^:private rule-cache
  ^{:doc "{:path env :rules {name-str → [rules]}}: extracted rules scoped to actual
          immutable Env identity, including local declarations and priority overlays."}
  (atom nil))

(defn capture-caches
  "Capture the immutable lazy simp-rule cache, without opening a store."
  []
  @rule-cache)

(defn validate-caches! [snapshot]
  (when-not (or (nil? snapshot)
                (and (map? snapshot) (contains? snapshot :path) (map? (:rules snapshot))))
    (throw (ex-info "Invalid simp-index cache snapshot" {})))
  snapshot)

(defn restore-caches! [snapshot]
  (reset! rule-cache (validate-caches! snapshot)))

(def ^:private extract-simp-lemma
  "simp's private CI → simp-rule extractor, resolved once on first use (var-accessed: this leaf
   must not require ansatz.tactic.simp)."
  (delay @(requiring-resolve 'ansatz.tactic.simp/extract-simp-lemma)))

(def ^:private default-simp-priority
  (delay @(requiring-resolve 'ansatz.tactic.simp/default-simp-priority)))

(defn- edn-safe-keys
  "Make a disc-tree key-path EDN-round-trippable: a :const key's `:name` is a kernel Name →
   stringify. Applied to BOTH stored and query keys so they compare consistently in the trie
   (same as ansatz.recall)."
  [ks]
  (mapv (fn [k] (if (instance? Name (:name k)) (update k :name nm/->string) k)) ks))

(defn lemma-lhs-keys
  "The disc-tree LHS key-path(s) for the simp rule(s) a lemma yields — keyed exactly as
   `build-lemma-index` (st+env arg-filtering), so a stored key matches the query keys simp
   produces. A name may yield several rules (And-split, etc.); one key-path per rule. Empty if
   the declaration is not a usable simp lemma."
  [st env ^ConstantInfo ci]
  (->> (@extract-simp-lemma env ci @default-simp-priority)
       (keep :lhs-pattern)
       (map #(edn-safe-keys (dt/expr->keys st env %)))
       (filter seq)
       vec))

(defn lemma-keys
  "The simp entries `[name key-str]` — one per rule — for every @[simp] lemma in `names`,
   resolved via `resolve-fn : name-str → ConstantInfo|nil` (a nil declaration is
   skipped, as is a key longer than `max-key-len`; keying errors propagate). The one-time, type-forcing keying pass
   the importer runs. Lemmas' rfl-flags come from their PROOFS, so the resolver must keep
   theorem values for these names (:keep-value?)."
  [names env resolve-fn & {:keys [max-key-len] :or {max-key-len 120}}]
  (let [st (tc/mk-tc-state env)]
    (into []
          (mapcat (fn [nam]
                    (let [ci (resolve-fn nam)
                          ks (when ci (lemma-lhs-keys st env ci))]
                      (keep (fn [k] (when (< (count k) max-key-len) [nam (pr-str k)])) ks))))
          names)))

(defn build-simp-trie
  "The `LHS-key → name` disc-tree from `[name key-str]` entries — trie-insert only. The
   importer persists the RESULT as the store's `:simp-trie` blob, so a session loads a trie
   (hundreds of ms) instead of rebuilding it (6 s for Mathlib's 90k keys)."
  [entries]
  (reduce (fn [trie [nam k]] (dt/trie-insert trie (edn/read-string k) nam))
          dt/empty-trie entries))

(defn ensure-simp-trie!
  "Use the Env's captured immutable base trie when present. Legacy sources keep
   their existing lazy global-store lookup; they do not acquire snapshot evidence."
  [env]
  (if-let [captured (env/get-extension env captured-index-key nil)]
    (do (when-not (.sameExternalView ^ansatz.kernel.Env env ^ansatz.kernel.Env (:view captured))
          (throw (ex-info "Captured simp index belongs to another external Env view" {})))
        (:trie captured))
    (when-let [{:keys [store-path branch] :as src} (index-source env)]
      (let [{cur-path :store-path cur-branch :branch store-map :store-map}
            @(deref (requiring-resolve 'ansatz.state/ansatz-store))]
        (when (and store-map (= cur-path store-path) (= cur-branch branch))
          (let [{:keys [source trie]} @state/ansatz-simp-trie]
            (if (= source src)
              trie
              (let [trie ((requiring-resolve 'ansatz.export.storage/read-derived)
                          (:store store-map) branch :simp-trie)]
                (reset! state/ansatz-simp-trie {:source src :trie trie})
                trie))))))))

;; ---- lookup side: candidate names by goal-subterm key, lazy rule resolution ----

(defn query-keys
  "The edn-safe disc-tree key-path for a goal subterm — the stored LHS keys' encoding, so
   `dt/trie-match` against the loaded trie compares equal."
  [st env expr]
  (edn-safe-keys (dt/expr->keys st env expr)))

(defn candidate-names
  "Lemma NAMES whose LHS structurally matches `expr` (over-approximate — the disc tree; simp's
   own pattern match is the exact gate). Deduped."
  [trie st env expr]
  (distinct (dt/trie-match trie (query-keys st env expr))))

(defn rules-for
  "The extracted simp rule(s) for lemma `name-str`, at its inherited @[simp] priority
   (ansatz.attrs' :simp-priorities extension, Lean's default otherwise), memoized per immutable Env identity.
   A missing declaration or an inapplicable lemma memoizes as []; errors propagate."
  [env name-str]
  (let [p env
        cache (let [c @rule-cache] (if (identical? (:path c) p) c (reset! rule-cache {:path p :rules {}})))]
    (if-let [hit (find (:rules cache) name-str)]
      (val hit)
      (let [prio (get (env/get-extension env :simp-priorities {}) name-str @default-simp-priority)
            rules (or (when-let [ci (env/lookup env (nm/from-string name-str))]
                        (@extract-simp-lemma env ci prio))
                      [])
            rules (vec rules)]
        (swap! rule-cache (fn [c] (if (identical? (:path c) p) (assoc-in c [:rules name-str] rules) c)))
        rules))))

(defn candidate-rules
  "Every rule of every lemma in `trie` whose LHS structurally matches `expr` — the lazily-served
   share of a simp call's candidate set."
  [trie st env expr]
  (into [] (mapcat #(rules-for env %)) (candidate-names trie st env expr)))
