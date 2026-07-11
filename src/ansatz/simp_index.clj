(ns ansatz.simp-index
  "Persistent SIMP INDEX: the disc-tree LHS keying of a store's @[simp] lemma
   corpus, dumped once as a store artifact (`<store>/simp-keys.ndjson.gz`) and
   rebuilt fast on boot. At Mathlib scale the inherited @[simp] set is ~90k
   lemmas that `simp` otherwise resolves+keys from PSS on EVERY call (~the
   recall-dump cost per simp — making full simp unusable). This is the recall
   pattern applied to simp: dump `name → LHS-key` offline, load a compact
   `key → name` trie, and at simp time look up candidate NAMES by the goal
   subterm's key, resolving+extracting the rewrite rule for only the handful
   that match (lazy, cached). Mirrors ansatz.recall; the loaded trie lives in
   ansatz.state/ansatz-simp-trie and is consumed by ansatz.tactic.simp.

   A dependency-light leaf: it reuses simp's own LHS extraction
   (`extract-simp-lemma`, via var) and disc-tree keying (`expr->keys`) so the
   stored keys match exactly what `build-lemma-index`/`lookup-simp-tree`
   produce at run time."
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.tactic.simp :as simp]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [clojure.java.io :as io]
            [clojure.edn :as edn])
  (:import [ansatz.kernel Name ConstantInfo]
           [java.util.zip GZIPInputStream GZIPOutputStream]))

(def ^:private extract-simp-lemma
  "simp's private CI → simp-rule extractor (var-accessed)."
  @#'simp/extract-simp-lemma)

(defn- edn-safe-keys
  "Make a disc-tree key-path EDN-round-trippable: a :const key's `:name` is a
   kernel Name → stringify. Applied to BOTH stored and query keys so they
   compare consistently in the trie. (Same as ansatz.recall.)"
  [keys]
  (mapv (fn [k] (if (instance? Name (:name k)) (update k :name nm/->string) k)) keys))

(defn lemma-lhs-keys
  "The disc-tree LHS key-path(s) for the simp rule(s) a lemma NAME yields —
   keyed exactly as `build-lemma-index` (st+env arg-filtering), so a stored key
   matches the query keys `lookup-simp-tree` produces. A name may yield several
   rules (And-split, etc.); returns one key-path per rule. nil if the name is
   not a usable simp lemma."
  [st env ^ConstantInfo ci]
  (->> (extract-simp-lemma env ci 1000)
       (keep :lhs-pattern)
       (map #(edn-safe-keys (dt/expr->keys st env %)))
       (filter seq)
       vec))

(defn dump-simp-keys!
  "Compute the LHS disc-tree key(s) for every @[simp] lemma in `names` (resolved
   via `resolve-fn : name-str → ConstantInfo|nil`) and write NDJSON.gz
   `{:name :key}` (one line per rule) to `path`. The one-time, type-forcing
   keying pass — amortized into a store artifact. Returns the number of keys
   written."
  [names env resolve-fn path & {:keys [max-key-len] :or {max-key-len 120}}]
  (let [st (tc/mk-tc-state env)]
    (with-open [w (io/writer (GZIPOutputStream. (io/output-stream (io/file path))))]
      (reduce
       (fn [n nam]
         (let [ci (try (resolve-fn nam) (catch Throwable _ nil))
               keys (when ci (try (lemma-lhs-keys st env ci) (catch Throwable _ nil)))]
           (reduce (fn [n k]
                     (if (< (count k) max-key-len)
                       (do (.write w (pr-str {:name nam :key (pr-str k)}))
                           (.write w "\n")
                           (inc n))
                       n))
                   n
                   (or keys []))))
       0 names))))

(defn load-simp-trie
  "Read a simp-keys NDJSON.gz and build the `LHS-key → name` disc-tree — fast
   (trie-insert only; the expensive keying was done at dump time). The trie
   values are lemma NAME strings; simp resolves+extracts the rule on demand."
  [path]
  (with-open [r (io/reader (GZIPInputStream. (io/input-stream (io/file path))))]
    (reduce (fn [trie line]
              (let [{:keys [name key]} (edn/read-string line)]
                (dt/trie-insert trie (edn/read-string key) name)))
            dt/empty-trie
            (line-seq r))))

;; ---- lookup side: candidate names by goal-subterm key, lazy rule resolution ----

(defn query-keys
  "The edn-safe disc-tree key-path for a goal subterm — same encoding as the
   stored LHS keys, so `dt/trie-match` against the loaded trie compares equal."
  [st env expr]
  (edn-safe-keys (dt/expr->keys st env expr)))

(defn candidate-names
  "Lemma NAMES whose LHS structurally matches `expr` (over-approximate — the
   disc tree; simp's own pattern match is the exact gate). Deduped."
  [name-trie st env expr]
  (distinct (dt/trie-match name-trie (query-keys st env expr))))

(defn resolve-rules
  "Resolve+extract the simp rule(s) for lemma `name-str`, memoized in `cache`
   (an atom map). Failures memoize as [] so a bad name is resolved once."
  [cache env name-str]
  (if-let [hit (find @cache name-str)]
    (val hit)
    (let [rules (or (try (when-let [ci (env/lookup env (nm/from-string name-str))]
                           (extract-simp-lemma env ci 1000))
                         (catch Throwable _ nil))
                    [])]
      (swap! cache assoc name-str (vec rules))
      (vec rules))))
