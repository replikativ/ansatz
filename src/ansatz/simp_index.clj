(ns ansatz.simp-index
  "Persistent @[simp] index: the disc-tree LHS keying of a store's @[simp] lemma corpus, dumped
   once as a store artifact (`<store>/simp-keys.ndjson.gz`) and rebuilt on first demand.

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
            [clojure.java.io :as io]
            [clojure.edn :as edn])
  (:import [ansatz.kernel Name ConstantInfo]
           [java.util.zip GZIPInputStream GZIPOutputStream]))

(defonce simp-keys-path
  ^{:doc "Path of the current store's simp-keys.ndjson.gz (set by ansatz.core/init!), or nil.
          The trie itself is built on first demand — see ensure-simp-trie!."}
  (atom nil))

(defonce ^:private rule-cache
  ^{:doc "name-str → vector of extracted simp rules, for the lazily-served corpus. A lemma's
          rules are stable for a store; cleared whenever the index is re-pointed."}
  (atom {}))

(defn reset-index!
  "Point the index at `path` (or nil: no artifact) and drop the trie and rule cache — called by
   ansatz.core/init! for every store switch so nothing from a previous store survives."
  [path]
  (reset! simp-keys-path path)
  (reset! state/ansatz-simp-trie nil)
  (reset! rule-cache {}))

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

(defn dump-simp-keys!
  "Compute the LHS disc-tree key(s) for every @[simp] lemma in `names` (resolved via
   `resolve-fn : name-str → ConstantInfo|nil`) and write NDJSON.gz `{:name :key}` (one line per
   rule) to `path`. The one-time, type-forcing keying pass — amortized into a store artifact.
   Returns the number of keys written."
  [names env resolve-fn path & {:keys [max-key-len] :or {max-key-len 120}}]
  (let [st (tc/mk-tc-state env)]
    (with-open [w (io/writer (GZIPOutputStream. (io/output-stream (io/file path))))]
      (reduce
       (fn [n nam]
         (let [ci (try (resolve-fn nam) (catch Throwable _ nil))
               ks (when ci (try (lemma-lhs-keys st env ci) (catch Throwable _ nil)))]
           (reduce (fn [n k]
                     (if (< (count k) max-key-len)
                       (do (.write w (pr-str {:name nam :key (pr-str k)}))
                           (.write w "\n")
                           (inc n))
                       n))
                   n
                   (or ks []))))
       0 names))))

(defn load-simp-trie
  "Read a simp-keys NDJSON.gz and build the `LHS-key → name` disc-tree — trie-insert only, the
   expensive keying was done at dump time (~6 s for Mathlib's 90k keys, dominated by EDN
   parsing). The trie values are lemma NAME strings; simp resolves+extracts rules on demand."
  [path]
  (with-open [r (io/reader (GZIPInputStream. (io/input-stream (io/file path))))]
    (reduce (fn [trie line]
              (let [{:keys [name key]} (edn/read-string line)]
                (dt/trie-insert trie (edn/read-string key) name)))
            dt/empty-trie
            (line-seq r))))

(defn ensure-simp-trie!
  "The simp trie for the current store, built on FIRST use and cached in
   ansatz.state/ansatz-simp-trie; nil when the store has no keys artifact (the eager path then
   serves the inherited set). A truncated/corrupt artifact degrades to nil, never throws."
  []
  (or @state/ansatz-simp-trie
      (when-let [p @simp-keys-path]
        (let [trie (try (load-simp-trie p)
                        (catch Throwable t
                          (println "WARN: simp index unreadable, skipping"
                                   "(re-dump with scripts/dump_simp_keys.clj):" (.getMessage t))
                          nil))]
          (when (nil? trie) (reset! simp-keys-path nil))
          (reset! state/ansatz-simp-trie trie)
          trie))))

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
   (ansatz.attrs' :simp-priorities extension, Lean's default otherwise), memoized for the
   session. A name that fails to resolve or extract memoizes as [] so it is tried once."
  [env name-str]
  (if-let [hit (find @rule-cache name-str)]
    (val hit)
    (let [prio (get (env/get-extension env :simp-priorities {}) name-str @default-simp-priority)
          rules (or (try (when-let [ci (env/lookup env (nm/from-string name-str))]
                           (@extract-simp-lemma env ci prio))
                         (catch Throwable _ nil))
                    [])
          rules (vec rules)]
      (swap! rule-cache assoc name-str rules)
      rules)))

(defn candidate-rules
  "Every rule of every lemma in `trie` whose LHS structurally matches `expr` — the lazily-served
   share of a simp call's candidate set."
  [trie st env expr]
  (into [] (mapcat #(rules-for env %)) (candidate-names trie st env expr)))
