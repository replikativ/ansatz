(ns ansatz.attrs
  "Inherit Lean's DECLARATION ATTRIBUTES (@[simp], @[csimp], @[extern], @[implemented_by], …) into
   ansatz Env extensions. These attributes are NOT part of the kernel export (lean4export emits only
   types + values), so `scripts/dump_attrs.lean` emits them as NDJSON — one
   {\"kind\":\"simp\",\"name\":\"…\"} per line — from the SAME Lean toolchain that produced the store.

   `import-attrs` loads them into the env, keeping only names that are constants actually present in
   the env, so version drift degrades gracefully (an absent lemma is simply skipped). The attributes
   become env EXTENSIONS (Lean's EnvironmentExtension), so they branch with the env:
     simp → :simp-lemmas   unfold → :simp-unfold   csimp → :csimp   extern → :extern
     class → :classes (Lean.Class.classExtension identity)
   plus :simp-priorities — {name → priority} for the @[simp] lemmas whose priority is NOT
   Lean's default (`@[simp low]` / `@[simp high]`). Priority is not decoration: `Bool.false_eq`
   and `Bool.true_eq` are confluent only because they are low.
   The tactic / optimizer / codegen layers can then consult the inherited set instead of hand-curating."
  (:require [ansatz.bundle :as bundle]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.state :as state]
            [ansatz.simp-sources :as simp-sources]
            [clojure.string :as str]
            [clojure.java.io :as io]))

(def ^:private kind->ext
  "Attribute kind (NDJSON \"kind\") → the Env extension key its entries accumulate into."
  {"simp" :simp-lemmas, "unfold" :simp-unfold, "unfold-thms" :simp-unfold-thms, "extern" :extern, "csimp" :csimp, "impl" :implemented-by, "class" :classes})

(def default-simp-priority
  "Lean's `eval_prio default` — the priority every @[simp] lemma has unless it says otherwise.
   ansatz's simp uses the same number (see ansatz.tactic.simp/make-simp-lemmas), so only the
   entries that DIFFER need carrying in the :simp-priorities extension."
  1000)

(def ^:private map-kinds
  "Kinds that carry a \"target\" (the replacement / impl decl) — stored as a {name → target} map.
   Equation-owner registrations carry a vector of theorem names in that slot.
   The rest are stored as sets of names."
  ;; Lean 4.33.1 Meta/Tactic/Simp/SimpTheorems.lean registerDeclToUnfoldThms:
  ;; record owner → equations separately; the corpus also registers each equation
  ;; as a simp theorem (Attr.lean addDeclToUnfold), with its own phase/priority.
  #{"csimp" "impl" "unfold-thms"})

(defn parse-attr-lines
  "Strict JSON lines → persisted `[kind name target prio]` tuples. Legacy simp
   rows may omit priority (nil). Unsupported native semantics, malformed/unknown
   fields and duplicate keys fail before any tuple is installed or name probed."
  [lines]
  (mapv (fn [line]
          (let [{:keys [kind name target prio theorems] :as row}
                (metadata/parse-attribute-row line {:legacy-priority? true})]
            (when (metadata/unsupported-attribute? row)
              (throw (ex-info "Unsupported native attribute semantics" {:kind kind :name name})))
            [kind name (if (= "unfold-thms" kind) theorems target) prio])) lines))

(defn- attribute-lines [text]
  (if (empty? text) []
      (let [lines (str/split text #"\r?\n" -1)]
        (if (= "" (peek lines)) (pop lines) lines))))

(defn- checked-tuples [tuples]
  (mapv (fn [tuple]
          (let [[kind declaration target priority] (when (sequential? tuple) tuple)
                valid-name? #(and (string? %) (not (str/blank? %)))]
            (when-not (and (sequential? tuple) (= 4 (count tuple))
                           (contains? kind->ext kind) (valid-name? declaration)
                           (cond
                             (= "unfold-thms" kind) (and (vector? target) (every? valid-name? target))
                             (map-kinds kind) (valid-name? target)
                             :else (nil? target))
                           (if (= "simp" kind)
                             (or (nil? priority) (and (integer? priority) (<= 0 priority metadata/max-priority)))
                             (nil? priority)))
              (throw (ex-info "Invalid persisted attribute tuple" {:kind kind :name declaration})))
            tuple)) tuples))

(defn import-attr-tuples
  "Return [env' stats]: `env` with `[kind name target prio]` tuples loaded into the matching
   extensions — keeping only names `present?` says are constants. csimp/impl become
   {name → target} maps (the f→g replacement / impl); the rest are name sets. `stats` maps each
   extension key to the count loaded, plus :skipped."
  [env tuples {:keys [present?]}]
  (let [tuples (checked-tuples tuples)
        present? (or present?
                     (fn [n] (some? (env/lookup env (name/from-string n)))))]
    (reduce (fn [[e stats] [k n target prio]]
              (if-let [ext-key (kind->ext k)]
                (if (present? n)
                  [(cond-> (if (map-kinds k)
                             (env/update-extension e ext-key {} assoc n target)
                             (env/update-extension e ext-key #{} conj n))
                     ;; Lean's simp PRIORITY, when the corpus records it. Only the
                     ;; non-default ones are worth carrying, and they are load-bearing:
                     ;; `Bool.false_eq`/`Bool.true_eq` are `@[simp low]` and rewrite each
                     ;; other's output, so at equal priority simp oscillates between
                     ;; `(false = true)` and `(true = false)` instead of letting
                     ;; `Bool.false_eq_true` (default priority) collapse it to `False`.
                     (and (= "simp" k) prio (not= prio default-simp-priority))
                     (env/update-extension :simp-priorities {} assoc n prio)
                     (= "simp" k) (simp-sources/mark-local-registration n))
                   (update stats ext-key (fnil inc 0))]
                  [e (update stats :skipped (fnil inc 0))])
                [e stats]))
            [env {}]
            tuples)))

(defn import-attrs
  "Return [env' stats] where env' is `env` with the attributes from `ndjson` (a file path, or a seq
   of NDJSON lines) loaded — see import-attr-tuples. Presence via env/lookup RESOLVES the
   declaration; for external (PSS-backed) stores pass a cheap membership `:present?`
   (see storage/contains-name-checker)."
  ([env ndjson] (import-attrs env ndjson {}))
  ([env ndjson opts]
   (let [lines (if (sequential? ndjson) ndjson (attribute-lines (slurp ndjson :encoding "UTF-8")))]
     (import-attr-tuples env (parse-attr-lines lines) opts))))

(defn import-attrs!
  "Load the attributes from `ndjson` into the GLOBAL env (atomically). Returns the load stats."
  ([ndjson] (import-attrs! ndjson {}))
  ([ndjson opts]
   (let [stats (atom nil)]
     (swap! state/ansatz-env (fn [e] (let [[e' s] (import-attrs e ndjson opts)] (reset! stats s) e')))
     @stats)))

(defn install-tuples!
  "Load already-filtered attr tuples (a store's derived `:attrs` blob) into the GLOBAL env.
   Every name in them is present by construction, so no presence probe."
  [tuples]
  (let [stats (atom nil)]
    (swap! state/ansatz-env (fn [e] (let [[e' s] (import-attr-tuples e tuples {:present? (constantly true)})]
                                      (reset! stats s) e')))
    @stats))

(defn read-attr-file
  "The tuples of an attrs corpus file — `.ndjson.gz` or plain `.ndjson` (what
   scripts/dump_attrs.lean writes). nil when the file does not exist."
  [path]
  (let [f (io/file path)]
    (when (.exists f)
      (let [text (if (str/ends-with? (.getName f) ".gz")
                   (with-open [in (java.util.zip.GZIPInputStream. (io/input-stream f))]
                     (slurp in :encoding "UTF-8"))
                   (slurp f :encoding "UTF-8"))]
        (parse-attr-lines (attribute-lines text))))))

(def ^:private bundled-attrs-resource "ansatz/init-attrs.ndjson.gz")

(defn bundled-attrs
  "Read verified bundled attribute tuples without changing proof state. Schema 2
   uses strictly decoded JSON rows and rejects unsupported native semantics."
  []
  (bundle/with-verified
    (fn [manifest]
      (bundle/assert-consumable!)
      (if (= "ansatz-bundle/2" (:bundle/schema manifest))
        (mapv (fn [{:keys [kind name target prio theorems]}]
                [kind name (if (= "unfold-thms" kind) theorems target) prio])
              (bundle/verified-companion-rows :attrs))
        (let [payload (bundle/verified-bytes bundled-attrs-resource)
              text (with-open [in (java.util.zip.GZIPInputStream. (java.io.ByteArrayInputStream. payload))]
                     (slurp in :encoding "UTF-8"))]
          (parse-attr-lines (attribute-lines text)))))))

(defn load-bundled-attrs!
  "Import verified bundled attribute tuples into the GLOBAL env, intersected
   with its declarations. Unsupported schema-2 semantics fail before mutation.
   Returns load stats; store imports retain their separate persisted tuple path."
  ([] (load-bundled-attrs! {}))
  ([opts]
   (let [tuples (bundled-attrs)
         stats (atom nil)]
     (swap! state/ansatz-env
            (fn [e]
              (let [[loaded result] (import-attr-tuples e tuples opts)]
                (reset! stats result)
                loaded)))
     @stats)))
