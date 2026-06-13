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
            [clojure.string :as str]))

(def ^:private kind->ext
  "Attribute kind (NDJSON \"kind\") → the Env extension key its names accumulate into (a set)."
  {"simp" :simp-lemmas, "unfold" :simp-unfold, "csimp" :csimp, "extern" :extern})

(defn- parse-line [l]
  (when-let [[_ k n] (re-find #"\"kind\":\"([^\"]+)\"[^}]*\"name\":\"([^\"]+)\"" l)]
    [k n]))

(defn import-attrs
  "Return [env' stats] where env' is `env` with the attributes from `ndjson` (a file path, or a seq
   of NDJSON lines) loaded into the matching extensions — keeping only names that are constants in
   `env`. `stats` maps each extension key to the count loaded, plus :skipped (names absent from env)."
  [env ndjson]
  (let [lines   (if (sequential? ndjson) ndjson (str/split-lines (slurp ndjson)))
        present? (fn [n] (some? (env/lookup env (name/from-string n))))]
    (reduce (fn [[e stats] [k n]]
              (if-let [ext-key (kind->ext k)]
                (if (present? n)
                  [(env/update-extension e ext-key #{} conj n) (update stats ext-key (fnil inc 0))]
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
