(ns ansatz.attrs
  "Inherit Lean's DECLARATION ATTRIBUTES (@[simp], @[csimp], @[extern], @[implemented_by], …) into
   ansatz Env extensions. These attributes are NOT part of the kernel export (lean4export emits only
   types + values), so `scripts/dump_attrs.lean` emits them as NDJSON — one
   {\"kind\":\"simp\",\"name\":\"…\"} per line — from the SAME Lean toolchain that produced the store.

   `import-attrs` loads them into the env, keeping only names that are constants actually present in
   the env, so version drift degrades gracefully (an absent lemma is simply skipped). The attributes
   become env EXTENSIONS (Lean's EnvironmentExtension), so they branch with the env:
     simp → :simp-lemmas   unfold → :simp-unfold   csimp → :csimp   extern → :extern
   The tactic / optimizer / codegen layers can then consult the inherited set instead of hand-curating."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.state :as state]
            [clojure.string :as str]
            [clojure.java.io :as io]))

(def ^:private kind->ext
  "Attribute kind (NDJSON \"kind\") → the Env extension key its entries accumulate into."
  {"simp" :simp-lemmas, "unfold" :simp-unfold, "extern" :extern, "csimp" :csimp, "impl" :implemented-by})

(def ^:private map-kinds
  "Kinds that carry a \"target\" (the replacement / impl decl) — stored as a {name → target} map.
   The rest are stored as sets of names."
  #{"csimp" "impl"})

(defn- parse-line [l]
  (when-let [[_ k n] (re-find #"\"kind\":\"([^\"]+)\"[^}]*\"name\":\"([^\"]+)\"" l)]
    [k n (second (re-find #"\"target\":\"([^\"]+)\"" l))]))

(defn import-attrs
  "Return [env' stats] where env' is `env` with the attributes from `ndjson` (a file path, or a seq
   of NDJSON lines) loaded into the matching extensions — keeping only names that are constants in
   `env`. csimp/impl become {name → target} maps (the f→g replacement / impl); the rest are name
   sets. `stats` maps each extension key to the count loaded, plus :skipped (names absent from env)."
  [env ndjson]
  (let [lines   (if (sequential? ndjson) ndjson (str/split-lines (slurp ndjson)))
        present? (fn [n] (some? (env/lookup env (name/from-string n))))]
    (reduce (fn [[e stats] [k n target]]
              (if-let [ext-key (kind->ext k)]
                (if (present? n)
                  [(if (map-kinds k)
                     (env/update-extension e ext-key {} assoc n target)
                     (env/update-extension e ext-key #{} conj n))
                   (update stats ext-key (fnil inc 0))]
                  [e (update stats :skipped (fnil inc 0))])
                [e stats]))
            [env {}]
            (keep parse-line lines))))

(defn import-attrs!
  "Load the attributes from `ndjson` into the GLOBAL env (atomically). Returns the load stats."
  [ndjson]
  (let [stats (atom nil)]
    (swap! state/ansatz-env (fn [e] (let [[e' s] (import-attrs e ndjson)] (reset! stats s) e')))
    @stats))

(def ^:private bundled-attrs-resource "ansatz/init-attrs.ndjson.gz")

(defn load-bundled-attrs!
  "Import the bundled Lean attribute corpus (the gzipped NDJSON dumped from Init by
   scripts/dump_attrs.lean) into the GLOBAL env's extensions, intersected with the loaded store.
   Called by ansatz.core/init! + load-init! so Lean's @[simp]/@[csimp]/@[extern] are inherited by
   default. No-op (returns nil) if the resource isn't on the classpath. Returns the load stats."
  []
  (when-let [res (io/resource bundled-attrs-resource)]
    (let [lines (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
                  (str/split-lines (slurp in)))]
      (import-attrs! lines))))

(defn load-store-attrs!
  "Import a STORE-LOCAL Lean attribute corpus — `<store-path>/attrs.ndjson.gz` (or plain
   `.ndjson`), if present — into the GLOBAL env's extensions, intersected with the loaded store.
   This is how a store LARGER than the bundled Init (e.g. Mathlib, with ~100k+ @[simp]) inherits
   its OWN attributes: dump it once with `scripts/dump_attrs.lean <Module>` into the store dir.
   Additive over load-bundled-attrs! (union — import is set/map merge). Returns the load stats, or
   nil if no store-local file exists. Called by ansatz.core/init! after load-bundled-attrs!."
  [store-path]
  (when store-path
    (let [gz  (io/file store-path "attrs.ndjson.gz")
          raw (io/file store-path "attrs.ndjson")]
      (cond
        (.exists gz)  (let [lines (with-open [in (java.util.zip.GZIPInputStream. (io/input-stream gz))]
                                    (str/split-lines (slurp in)))]
                        (import-attrs! lines))
        (.exists raw) (import-attrs! (.getPath raw))))))
