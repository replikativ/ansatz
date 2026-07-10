(ns ansatz.recall
  "Persistent RECALL projection: the disc-tree keying of a store's declaration
   CONCLUSIONS, dumped once as a store artifact (`<store>/discr-keys.ndjson.gz`)
   and rebuilt fast on boot — so mathlib-scale recall costs seconds, not the
   ~13 min of re-keying every session (each key forces the decl's type DAG out
   of PSS). Mirrors the attrs/instances/matchers store-artifact pattern. A
   dependency-light leaf (dt + kernel only); consumers read the loaded trie
   from ansatz.state/ansatz-discr-trie."
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [clojure.edn :as edn])
  (:import [ansatz.kernel ConstantInfo Name]
           [java.util.zip GZIPInputStream GZIPOutputStream]))

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

(defn dump-discr-keys!
  "Compute the conclusion disc-tree key for every USEFUL decl in `decl-names`
   (resolved via `resolve-fn : name-str → ConstantInfo|nil`) and write
   NDJSON.gz `{:name :key}` to `path`. This is the one-time, type-forcing keying
   pass — amortized into a store artifact. Returns the number of keys written."
  [decl-names resolve-fn path & {:keys [max-key-len] :or {max-key-len 120}}]
  (with-open [w (io/writer (GZIPOutputStream. (io/output-stream (io/file path))))]
    (reduce
     (fn [n nam]
       (if-not (useful? nam)
         n
         (let [ci (try (resolve-fn nam) (catch Throwable _ nil))
               ks (when ci (try (decl-key (.type ^ConstantInfo ci)) (catch Throwable _ nil)))]
           (if (and ks (< (count ks) max-key-len))
             (do (.write w (pr-str {:name nam :key (pr-str ks)})) (.write w "\n") (inc n))
             n))))
     0 decl-names)))

(defn load-discr-trie
  "Read a discr-keys NDJSON.gz and build the disc-tree — fast (trie-insert only;
   the expensive keying was done at dump time). Returns the trie."
  [path]
  (with-open [r (io/reader (GZIPInputStream. (io/input-stream (io/file path))))]
    (reduce (fn [trie line]
              (let [{:keys [name key]} (edn/read-string line)]
                (dt/trie-insert trie (edn/read-string key) name)))
            dt/empty-trie
            (line-seq r))))
