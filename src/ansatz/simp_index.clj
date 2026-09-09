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

(def extension-key
  "The Env extension carrying the store's simp-keys artifact path (set by ansatz.core/init!).
   It rides on the immutable Env like the attrs extensions do, so an env built any other way
   (replay, a test fixture's `reset!`) has NO index and stays on the eager path — the index can
   never leak from one store's env into another's."
  :simp-keys-path)

(defn index-path
  "The simp-keys artifact path recorded on `env`, or nil."
  [env] (env/get-extension env extension-key nil))

(defn with-index-path
  "`env` with its simp-keys artifact path set (nil clears it)."
  [env path] (env/update-extension env extension-key nil (constantly path)))

(defonce ^:private rule-cache
  ^{:doc "{:path p :rules {name-str → [rules]}}: extracted rules for the lazily-served corpus,
          valid for the artifact they were resolved against (a lemma's rules are stable for a
          store); dropped when the path changes."}
  (atom nil))

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
  "The simp trie for `env`'s store, built on FIRST use and cached in
   ansatz.state/ansatz-simp-trie (keyed by the artifact path, so switching stores reloads);
   nil when the env records no artifact (the eager path then serves the inherited set). A
   truncated/corrupt artifact degrades to nil for the session, never throws."
  [env]
  (when-let [p (index-path env)]
    (let [{:keys [path trie]} @state/ansatz-simp-trie]
      (if (= path p)
        trie
        (let [trie (try (load-simp-trie p)
                        (catch Throwable t
                          (println "WARN: simp index unreadable, skipping"
                                   "(re-dump with scripts/dump_simp_keys.clj):" (.getMessage t))
                          nil))]
          (reset! state/ansatz-simp-trie {:path p :trie trie})
          trie)))))

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
   (ansatz.attrs' :simp-priorities extension, Lean's default otherwise), memoized per artifact.
   A name that fails to resolve or extract memoizes as [] so it is tried once."
  [env name-str]
  (let [p (index-path env)
        cache (let [c @rule-cache] (if (= (:path c) p) c (reset! rule-cache {:path p :rules {}})))]
    (if-let [hit (find (:rules cache) name-str)]
      (val hit)
      (let [prio (get (env/get-extension env :simp-priorities {}) name-str @default-simp-priority)
            rules (or (try (when-let [ci (env/lookup env (nm/from-string name-str))]
                             (@extract-simp-lemma env ci prio))
                           (catch Throwable _ nil))
                      [])
            rules (vec rules)]
        (swap! rule-cache (fn [c] (if (= (:path c) p) (assoc-in c [:rules name-str] rules) c)))
        rules))))

(defn candidate-rules
  "Every rule of every lemma in `trie` whose LHS structurally matches `expr` — the lazily-served
   share of a simp call's candidate set."
  [trie st env expr]
  (into [] (mapcat #(rules-for env %)) (candidate-names trie st env expr)))
