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
     reducibility → :reducibility-status (name → Lean ReducibilityStatus string)
     recursive → :recursive-defs, smart-unfolding → :smart-unfolding-defs
   plus :simp-priorities — {name → priority} for the @[simp] lemmas whose priority is NOT
   Lean's default (`@[simp low]` / `@[simp high]`). Priority is not decoration: `Bool.false_eq`
   and `Bool.true_eq` are confluent only because they are low.
   A simp row's origin (Lean `Origin.decl n post inv`) decides where it goes: the default
   (post, forward) is a :simp-lemmas name; `@[simp ↓]` / `@[simp ←]` rows are recorded in
   :simp-origins {name → #{{:post :inv :prio}}}; origins a later registration of the converse
   erased are in :simp-erased #{[name inv]} (Lean's `erased`) with their entries in
   :simp-masked. See add-simp-entry. Replay identifies an entry by name, phase and direction:
   Lean identifies tree entries by proof, so two inverse registrations of one theorem in
   different modules (distinct auxiliary proofs) can both survive in Lean, while here the later
   priority replaces the earlier — a limit of the dump's per-row shape.
   The tactic / optimizer / codegen layers can then consult the inherited set instead of hand-curating."
  (:require [ansatz.bundle :as bundle]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.state :as state]
            [ansatz.simp-sources :as simp-sources]
            [ansatz.tactic.simp.simp-theorems :as simp-theorems]
            [ansatz.tactic.simp.simproc :as simproc]
            [ansatz.kernel.tc :as tc]
            [clojure.string :as str]
            [clojure.java.io :as io]))

(def ^:private kind->ext
  "Attribute kind (NDJSON \"kind\") → the Env extension key its entries accumulate into."
  {"simp" :simp-lemmas, "unfold" :simp-unfold, "unfold-thms" :simp-unfold-thms,
   "extern" :extern, "csimp" :csimp, "impl" :implemented-by, "class" :classes,
   "reducibility" :reducibility-status, "recursive" :recursive-defs, "smart-unfolding" :smart-unfolding-defs})

(def default-simp-priority
  "Lean's `eval_prio default` — the priority every @[simp] lemma has unless it says otherwise.
   ansatz's simp uses the same number (see ansatz.tactic.simp/make-simp-lemmas), so only the
   entries that DIFFER need carrying in the :simp-priorities extension."
  1000)

(def ^:private map-kinds
  "Kinds that carry a \"target\" (the replacement / impl decl) — stored as a {name → target} map.
   Equation owners carry theorem vectors there; reducibility carries a status string.
   The rest are stored as sets of names."
  ;; Lean 4.33.1 Meta/Tactic/Simp/SimpTheorems.lean registerDeclToUnfoldThms:
  ;; record owner → equations separately; the corpus also registers each equation
  ;; as a simp theorem (Attr.lean addDeclToUnfold), with its own phase/priority.
  #{"csimp" "impl" "unfold-thms" "reducibility"})

(defn row->tuple
  "A validated attribute row → its persisted tuple `[kind name target prio]`, plus a fifth
   element `{:post bool :inv bool}` for a simp row whose origin is not the default
   (Lean `Origin.decl n post inv`, SimpTheorems.lean:69-91). Default rows keep the 4-tuple, so a
   corpus without pre/inverse rows persists exactly as before, and an older reader — whose
   tuple check requires 4 elements — fails on a 5-tuple instead of installing it as a forward
   post rule."
  [{:keys [kind name target prio theorems status] :as row}]
  (let [tuple [kind name (case kind "unfold-thms" theorems "reducibility" status target) prio]]
    (if-let [origin (metadata/simp-origin row)]
      (conj tuple origin)
      tuple)))

(defn parse-attr-lines
  "Strict JSON lines → persisted attribute tuples (row->tuple). Legacy simp rows may omit
   priority (nil) and phase/direction (default origin). Unsupported native semantics,
   malformed/unknown fields and duplicate keys fail before any tuple is installed or name
   probed. The result's metadata records `:simp-origin-fields?` — whether any simp row
   carried Lean's post/inv fields (a legacy dump has none)."
  [lines]
  (let [origin-fields? (volatile! false)
        tuples (mapv (fn [line]
                       (let [{:keys [kind name] :as row}
                             (metadata/parse-attribute-row line {:legacy-priority? true})]
                         (when (metadata/unsupported-attribute? row)
                           (throw (ex-info "Unsupported native attribute semantics" {:kind kind :name name})))
                         (when (and (= "simp" kind) (contains? row :post)) (vreset! origin-fields? true))
                         (row->tuple row))) lines)]
    (with-meta tuples {:simp-origin-fields? @origin-fields?})))

(defn- attribute-lines [text]
  (if (empty? text) []
      (let [lines (str/split text #"\r?\n" -1)]
        (if (= "" (peek lines)) (pop lines) lines))))

(defn- valid-simp-origin?
  "A persisted 5th tuple element: exactly {:post bool :inv bool}, never the default origin
   (which is written as the plain 4-tuple)."
  [origin]
  (and (map? origin) (= #{:post :inv} (set (keys origin)))
       (boolean? (:post origin)) (boolean? (:inv origin))
       (not (and (:post origin) (not (:inv origin))))))

(defn- checked-tuples [tuples]
  (mapv (fn [tuple]
          (let [[kind declaration target priority origin] (when (sequential? tuple) tuple)
                valid-name? #(and (string? %) (not (str/blank? %)))]
            (when-not (and (sequential? tuple)
                           (or (= 4 (count tuple))
                               (and (= 5 (count tuple)) (= "simp" kind) (valid-simp-origin? origin)))
                           (contains? kind->ext kind) (valid-name? declaration)
                           (cond
                             (= "reducibility" kind) (contains? metadata/reducibility-statuses target)
                             (= "unfold-thms" kind) (and (vector? target) (every? valid-name? target))
                             (map-kinds kind) (valid-name? target)
                             :else (nil? target))
                           (if (= "simp" kind)
                             (or (nil? priority) (and (integer? priority) (<= 0 priority metadata/max-priority)))
                             (nil? priority)))
              (throw (ex-info "Invalid persisted attribute tuple" {:kind kind :name declaration})))
            tuple)) tuples))

(defn simp-registered?
  "Lean `lemmaNames.contains (.decl n _ inv)` for the inherited @[simp] state: a visible entry
   of that name and direction, or an erased origin registered again (:simp-erased-registered)."
  [e n inv]
  (or (and (not inv) (contains? (env/get-extension e :simp-lemmas #{}) n))
      (boolean (some #(= inv (:inv %)) (get (env/get-extension e :simp-origins {}) n)))
      (contains? (env/get-extension e :simp-erased-registered #{}) [n inv])))

(defn- erase-simp-origin
  "Lean eraseCore (SimpTheorems.lean:612-622) on the inherited state: the origin key
   `[n inv]` is erased and unregistered; its entries move to :simp-masked {name → #{entry}},
   kept so that an explicit `simp [n]` (uneraseSimpEntry) can restore them in their phases."
  [e n inv]
  (let [prio (get (env/get-extension e :simp-priorities {}) n default-simp-priority)
        fwd? (and (not inv) (contains? (env/get-extension e :simp-lemmas #{}) n))
        moving (cond-> (into #{} (filter #(= inv (:inv %))) (get (env/get-extension e :simp-origins {}) n))
                 fwd? (conj {:post true :inv false :prio prio}))]
    (cond-> (-> e
                (env/update-extension :simp-erased #{} conj [n inv])
                (env/update-extension :simp-erased-registered #{} disj [n inv])
                (env/update-extension :simp-origins {}
                                      (fn [m] (let [os (into #{} (remove #(= inv (:inv %))) (get m n))]
                                                (if (seq os) (assoc m n os) (dissoc m n))))))
      fwd? (-> (env/update-extension :simp-lemmas #{} disj n)
               (env/update-extension :simp-priorities {} dissoc n))
      (seq moving) (env/update-extension :simp-masked {} update n (fnil into #{}) moving))))

(defn- with-entry
  "Lean DiscrTree.insertKeyValue replaces the value equal to the new one (same proof at the same
   keys): a re-registration in the same phase and direction replaces the earlier priority."
  [entries entry]
  (conj (into #{} (remove #(and (= (:post %) (:post entry)) (= (:inv %) (:inv entry)))) entries)
        entry))

(defn- add-simp-entry
  "Lean SimpTheorems.addSimpTheorem (SimpTheorems.lean:643-652) replayed for one inherited
   @[simp] tuple, in corpus (module) order:
   - first erase the registered converse, in EITHER direction (eraseFwdIfBwd, :634-638);
   - then register the origin; an erased origin stays erased — addSimpTheorem never un-erases
     (only `simp [n]` does, :702-705) — so its entry goes to :simp-masked;
   - a visible default origin (post, forward) is a :simp-lemmas name with its priority in
     :simp-priorities, as before; any other visible origin is an entry in
     :simp-origins {name → #{{:post :inv :prio}}} with its own priority.
   :simp-erased holds Lean's `erased` (which also hides an origin a persistent index still
   serves); :simp-erased-registered the erased origins registered again."
  [e n prio origin]
  (let [post (boolean (:post origin true)) inv (boolean (:inv origin false))
        prio (or prio default-simp-priority)
        entry {:post post :inv inv :prio prio}
        e (if (simp-registered? e n (not inv)) (erase-simp-origin e n (not inv)) e)]
    (cond
      (contains? (env/get-extension e :simp-erased #{}) [n inv])
      (-> e
          (env/update-extension :simp-erased-registered #{} conj [n inv])
          (env/update-extension :simp-masked {} update n with-entry entry))
      (and post (not inv))
      (cond-> (env/update-extension e :simp-lemmas #{} conj n)
        ;; Lean's simp PRIORITY, when the corpus records it. Only the
        ;; non-default ones are worth carrying, and they are load-bearing:
        ;; `Bool.false_eq`/`Bool.true_eq` are `@[simp low]` and rewrite each
        ;; other's output, so at equal priority simp oscillates between
        ;; `(false = true)` and `(true = false)` instead of letting
        ;; `Bool.false_eq_true` (default priority) collapse it to `False`.
        (not= prio default-simp-priority) (env/update-extension :simp-priorities {} assoc n prio)
        (= prio default-simp-priority) (env/update-extension :simp-priorities {} dissoc n))
      :else
      (env/update-extension e :simp-origins {} update n with-entry entry))))

(defn import-attr-tuples
  "Return [env' stats]: `env` with attribute tuples loaded into the matching extensions —
   keeping only names `present?` says are constants. csimp/impl become {name → target} maps
   (the f→g replacement / impl); simp tuples replay Lean's addSimpTheorem (add-simp-entry);
   the rest are name sets. `stats` maps each extension key to the count loaded (non-default
   simp origins count as :simp-origins), plus :skipped."
  [env tuples {:keys [present?]}]
  (let [tuples (checked-tuples tuples)
        present? (or present?
                     (fn [n] (some? (env/lookup env (name/from-string n)))))]
    (reduce (fn [[e stats] [k n target prio origin]]
              (if-let [ext-key (kind->ext k)]
                (if (present? n)
                  [(cond
                     (= "simp" k) (-> (add-simp-entry e n prio origin)
                                      (simp-sources/mark-local-registration n))
                     (map-kinds k) (env/update-extension e ext-key {} assoc n target)
                     :else (env/update-extension e ext-key #{} conj n))
                   (update stats (if origin :simp-origins ext-key) (fnil inc 0))]
                  [e (update stats :skipped (fnil inc 0))])
                [e stats]))
            [env {}]
            tuples)))

(defn forward-simp-names
  "The names whose replayed @[simp] state (import-attr-tuples) has a visible forward post
   origin: exactly the rules a persistent simp index keys. Pre-phase and inverse origins are
   served eagerly instead (ansatz.simp-index/eager-origins); erased (masked) ones only when an
   explicit `simp [n]` restores them."
  [tuples]
  (let [[e _] (import-attr-tuples (env/empty-env) (filterv #(= "simp" (first %)) tuples)
                                  {:present? (constantly true)})]
    (env/get-extension e :simp-lemmas #{})))

(defn live-forward-priorities
  "{name → priority} of the replayed visible forward post @[simp] rules — the rules a persistent
   index keys — for catalogue scalars that must agree with what simp serves."
  [tuples]
  (let [[e _] (import-attr-tuples (env/empty-env) (filterv #(= "simp" (first %)) tuples)
                                  {:present? (constantly true)})
        prios (env/get-extension e :simp-priorities {})]
    (into {} (map (fn [n] [n (get prios n default-simp-priority)]))
          (env/get-extension e :simp-lemmas #{}))))

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
        (mapv row->tuple (bundle/verified-companion-rows :attrs))
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

;; ── Named simp sets (Lean's `register_simp_attr`) ────────────────────────────────────────
;; Lean Meta/Tactic/Simp/RegisterCommand.lean `register_simp_attr s` makes a simp extension `s`;
;; `attribute [s] d` adds a declaration to it, and Elab/Tactic/Simp.lean resolveSimpIdTheorem?
;; reads an identifier that names no constant as a set: `simp [s]` uses its members. Here a set
;; is the :simp-sets extension {set-name → [declaration-name …]}: a theorem is a rewrite rule,
;; a definition is unfolded (its equation lemmas, as `simp [d]`). It branches with the env.

(defn- simp-set-member
  "A member as stored: a name string (Lean's default origin) or, for `attribute [s ↓]` /
   `[s ←]`, an origin {:name n :post p :inv i} (Lean SimpEntry.thm with Origin.decl n post inv)."
  [entry]
  (if (map? entry)
    (let [post (boolean (:post entry true)) inv (boolean (:inv entry false))
          n (str (:name entry))]
      (if (and post (not inv)) n {:name n :post post :inv inv}))
    (str entry)))

(defn- prop-decl?
  "Lean `isProp info.type` (Meta/Tactic/Simp/Attr.lean:53)."
  [env n]
  (when-let [ci (env/lookup env (name/from-string n))]
    (meta/prop? (tc/mk-tc-state env) (.type ^ansatz.kernel.ConstantInfo ci))))

(defn add-to-simp-set
  "`env` with the declarations `names` registered in the simp set `set-name` (Lean
   `attribute [set-name] names…`), in order. An entry is a name (string or symbol) or an origin
   {:name n :post bool :inv bool} (`attribute [set-name ↓ ←] n`). The members are the set's
   registration log; simp-theorems/replay-set gives its state (Lean addSimpTheorem: a later
   converse registration erases the earlier one, in either direction). `←` on a definition is
   rejected as Lean's attribute does (Attr.lean:18-21). An inverse member is resolved and
   preprocessed when it is registered — a declaration Ansatz derives on demand (Nat.ble_eq,
   Nat packing: simp/ensure-derivable) first — so a pending or irreversible `←` entry never
   enters the replay."
  [env set-name names]
  (let [ensure (requiring-resolve 'ansatz.tactic.simp/ensure-derivable)
        [env members]
        (reduce (fn [[env members] entry]
                  (let [m (simp-set-member entry)
                        n (when (map? m) (:name m))
                        env (if (:inv m) (ensure env n) env)]
                    (when (:inv m)
                      ;; Lean resolves the declaration before applying an attribute
                      (when-not (env/lookup env (name/from-string n))
                        (throw (ex-info (str "Unknown constant: " n) {:kind :elab-error :name n})))
                      (when-not (prop-decl? env n)
                        (throw (ex-info (str "Invalid `←` modifier: `" n "` is a declaration name to be unfolded")
                                        {:kind :elab-error :name n})))
                      ;; Lean preprocesses at registration (SimpTheorems.lean:726-729): an
                      ;; irreversible theorem is rejected before it can mask anything
                      ((requiring-resolve 'ansatz.tactic.simp/make-simp-lemmas) env [{:name n :inv true}]))
                    [env (if (= m (peek members)) members (conj members m))]))
                [env (get (env/get-extension env :simp-sets {}) (str set-name) [])] names)]
    (env/update-extension env :simp-sets {} assoc (str set-name) members)))

(defn- ignore-equations?
  "Lean Simp.ignoreEquations (SimpTheorems.lean:535-536): a projection function or a reducible
   definition (ReducibilityAttrs isReducible, metadata over the abbrev hint)."
  [env n]
  (or (some? (meta/projection-fn-info env n)) (meta/reducible-const? env n)))

(defn- expand-set-member
  "What `attribute [s ↓ ←] n` registers (Meta/Tactic/Simp/Attr.lean:43-56): a simproc goes to
   the set's simproc extension; a proposition is one theorem at the custom attribute's own
   default priority (not the default set's); a definition goes through addDeclToUnfold."
  [env {:keys [name post inv] :as entry}]
  (cond
    (simproc/is-builtin-simproc name) {:simprocs [{:name name :post post}]}
    (or (prop-decl? env name) (nil? (env/lookup env (ansatz.kernel.name/from-string name))))
    {:theorems [(assoc entry :prio default-simp-priority)]}
    :else (simp-theorems/attr-entries-of-decl env name post default-simp-priority
                                              #(ignore-equations? env %))))

(def ^:private set-state-cache
  "simp-set-entries for one immutable Env identity (a single slot, like simp-index/rules-for):
   a simp call reads its sets' states several times, and each replay expands every member. A
   staged Env (Env.isStaged) is not cached: its declarations become visible on the same object."
  (atom {:env nil :states {}}))

(defn simp-set-entries
  "The simp set `set-name`'s replayed state {:entries [{:name :post :inv :prio}] :erased
   :to-unfold :simprocs} (Lean's SimpTheorems and simprocs of that extension), or nil when no
   such set exists."
  [env set-name]
  (when-let [members (get (env/get-extension env :simp-sets {}) (str set-name))]
    (let [k (str set-name)
          replay #(simp-theorems/replay-set members (fn [m] (expand-set-member env m)))]
      (if (.isStaged ^ansatz.kernel.Env env)
        (replay)
        (let [cache (let [c @set-state-cache]
                      (if (identical? (:env c) env) c (reset! set-state-cache {:env env :states {}})))]
          (if-let [hit (find (:states cache) k)]
            (val hit)
            (let [state (replay)]
              (swap! set-state-cache (fn [c] (if (identical? (:env c) env) (assoc-in c [:states k] state) c)))
              state)))))))

(defn simp-set
  "The names of the simp set `set-name`'s members in `env` (strings, registration order, without
   duplicates; a member erased by a later converse registration is left out), or nil when no such
   set exists. simp-set-entries carries origins, equations and simprocs."
  [env set-name]
  (when-let [members (get (env/get-extension env :simp-sets {}) (str set-name))]
    ;; the erasures of the expanded replay: a definition's generated equations count
    (let [{:keys [erased]} (simp-set-entries env set-name)]
      (->> members
           (map simp-theorems/set-member->entry)
           (remove #(contains? erased [(:name %) (:inv %)]))
           (map :name) distinct vec))))
