;; Verified Clojure programming via Ansatz.
;;
;; Write Clojure functions with Ansatz types. Prove properties. Run at native speed.
;;
;; (ansatz/init! "path/to/store" "branch")
;; (ansatz/defn ^Nat double [^Nat n] (+ n n))
;; (ansatz/theorem add-zero [n Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))
;; (double 21)  ;; => 42, native speed

(ns ansatz.core
  "Verified Clojure — write proven programs using Ansatz types and tactics."
  (:refer-clojure :exclude [defn])
  (:require [clojure.java.io]
            [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.ac :as ac]
            [ansatz.export.storage :as storage]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.tactic.instance :as instance]
            [ansatz.inductive :as inductive]
            [ansatz.surface.match :as surface-match]
            [ansatz.surface.ingest :as ingest]
            [ansatz.surface.elaborate :as elab]
            [ansatz.codegen :as codegen]
            [ansatz.wf :as wf]
            [ansatz.attrs :as attrs]
            [ansatz.matchers :as matchers]
            [ansatz.state :as state]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; State
;; ============================================================

;; The DSL/elaboration verbosity flag (a/*verbose*, bound by wandler/tests). Stays interned in core
;; so the qualified handle resolves; ansatz.wf reads it dynamically via requiring-resolve.
(def ^:dynamic *verbose* true)

;; ============================================================
;; ProofContext — persistent value for proof/elaboration state
;; ============================================================
;; Lean 4 uses mutable refs to persistent data structures with save/restore.
;; We use a Clojure record (persistent value) held in a global atom for
;; REPL convenience. Tests and programmatic use can create isolated contexts.

(defrecord ProofContext [env instance-index synth-cache])

(clojure.core/defn make-context
  "Create a fresh ProofContext from an env and instance index."
  [env instance-index]
  (->ProofContext env instance-index (atom {})))

(clojure.core/defn fork-context
  "Fork a ProofContext for isolation. Creates a new env copy (via Env.fork)
   and fresh synth-cache. Instance index is shared (read-only)."
  [^ProofContext ctx]
  (->ProofContext (env/fork (:env ctx))
                  (:instance-index ctx)
                  (atom {})))

;; Global atoms — REPL convenience wrappers around ProofContext. The atoms live in the
;; dependency-free ansatz.state leaf (so extracted namespaces — codegen, wf — read/mutate the
;; live env without a core↔X cycle); re-exported here as the SAME atoms (a/ansatz-env is the
;; wandler-facing handle, swapped/reset by the runtime).
(def ansatz-env state/ansatz-env)
(def ansatz-instance-index state/ansatz-instance-index)

;; Extensible registries — declared early so the elaboration/codegen layers can reference them.
;; Lean 4 equivalents: @[tactic], @[simproc], elab_rules
(defonce ^{:doc "Open tactic registry. Maps symbol → (fn [ps args] → ps')."} tactic-registry (atom {}))
(defonce ^{:doc "Persistent simproc registry. Vector of (fn [st expr] → result|nil)."} simproc-registry (atom []))
;; Arity + codegen registries live in ansatz.surface.ingest (the shared leaf that breaks the
;; core↔codegen cycle); ansatz->clj (now in ansatz.codegen) reads them there. Re-exported here —
;; SAME atoms; a/arity-registry / a/codegen-registry keep resolving (wandler swaps a/codegen-registry).
(def arity-registry ingest/arity-registry)
;; Structure registry — maps type-name → {:fields [field-name ...], :ctor-sym symbol}
;; Used by ansatz->clj to compile constructors to defrecord and projections to keyword access.
;; Re-exported from ansatz.surface.ingest (the shared low-level ns that breaks the
;; core↔elaborate dependency cycle). Same atom — registration and projection agree.
(def structure-registry ingest/structure-registry)

;; ── Runtime seams (filled additively by wandler) ────────────────────────────────────────────────
;; ansatz.core is the DSL: it elaborates surface Clojure to kernel terms, kernel-checks them, and
;; codegens the base (Nat/Int/inductive/record) fragment. A runtime layer (wandler) plugs in a
;; certified OPTIMIZER and the COLLECTION/relational codegen through these seams — without ansatz
;; depending on it, and leaving ansatz-alone a/defn fully runnable.
;; SEAM — optimizer: nil, or (fn [env term] → term') where term' is kernel-EQUAL to term (the hook
;; certifies optimized ≡ original itself). define-verified runs it on the elaborated body just before
;; codegen; the ORIGINAL term stays in the env (the proven definition).
(defonce ^{:doc "Optimizer hook for the runtime. nil or (fn [env name term] → term')."} optimize-hook (atom nil))
;; SEAM — codegen: head-constant Name-string → (fn [env expr names] → clj-form). ansatz->clj consults
;; it for application heads it does not lower natively (e.g. List.map → wandler's amapl). Base kernel
;; codegen stays in ansatz; the runtime adds collection/relational lowering additively.
;; The atom lives in ansatz.surface.ingest (shared leaf); re-exported here as the named seam.
(def codegen-registry ingest/codegen-registry)

;; ── Incremental Clojure ingestion ───────────────────────────────────────────────────────────────
;; The elaborator macroexpand-1's ANY clojure.core (or user) macro on the way in — so all the
;; binding/threading/sugar reaches the kernel as core forms (let*/fn*/if/application) without a case
;; per macro — EXCEPT a small exclusion set: forms ansatz handles with a dedicated typed elaborator
;; that beats the macro's expansion. Today that set is just `cond`: the elaborator's typed cond
;; handler maps :else correctly, unlike Clojure's :else-as-truthy expansion. (`=>` is the type
;; arrow; `->` threads as in Clojure.)
;; Soundness does NOT depend on this set: the kernel type-checks every resulting term, so a macro
;; that expands to a non-CIC form simply fails to elaborate (an honest error) — it can never produce
;; an unsound definition. The set only keeps OUR handlers winning and errors clean.
;; Re-exported from ansatz.surface.ingest (shared, breaks the core↔elaborate cycle).
(def no-expand-macros ingest/no-expand-macros)
(def expand-macro? ingest/expand-macro?)

(declare init!* init!-bundled-medium!)

(clojure.core/defn init!
  "Load an Ansatz environment and build the instance index.

   0-arity `(init!)` — ZERO-SETUP: load the bundled MEDIUM Init tier (~2997 Lean
   `Init` declarations) straight from the jar, in TRUST mode. Enough for ordinary
   verified `defn`/`theorem` over Nat/List/Bool with no store to build. Also via
   the name \"medium\".

   1-arity `(init! \"init\"|\"mathlib\"|…)` — a store NAME resolved via ansatz.store:
   the durable data-root ($ANSATZ_STORE_DIR → $XDG_DATA_HOME/ansatz/stores →
   ~/.local/share/ansatz/stores) first, then the legacy /var/tmp/ansatz-<name>.
   This is the full, kernel-verified tier; a missing named store is an honest error
   (it does NOT silently fall back to the bundled medium tier).

   2-arity `(init! store-path branch)` — load from an explicit store path."
  ([] (init!-bundled-medium!))
  ([store-name]
   (if (contains? #{"medium" "init-medium"} (name store-name))
     (init!-bundled-medium!)
     (let [path (or ((requiring-resolve 'ansatz.store/resolve-existing) store-name)
                    (throw (ex-info (str "No store named '" store-name "' found. Run "
                                         "./scripts/setup-" (name store-name) ".sh to build it, "
                                         "or call (init!) for the bundled medium tier.")
                                    {:store store-name})))]
       (init! path (name store-name)))))
  ([store-path branch]
   (init!* store-path branch)))

(clojure.core/defn- setup-env!
  "Install global proof state from an already-loaded `env`: reset the env atom,
   inherit Lean's bundled @[simp]/@[csimp]/@[extern] + Match.MatcherInfo, and build
   the instance index. `store-path` is the store dir (for store-local attrs + the
   complete instances.tsv) or nil for the bundled in-memory tier (→ name-based
   instance discovery from the env)."
  [env store-path]
  (reset! ansatz-env env)
  (attrs/load-bundled-attrs!)              ;; inherit Lean's Init @[simp]/@[csimp]/@[extern]
  (when store-path
    (attrs/load-store-attrs! store-path))  ;; + this store's OWN attrs (e.g. Mathlib) if dumped alongside
  (matchers/load-bundled-matchers!)        ;; inherit Lean's Match.MatcherInfo (for the `split` tactic)
  ;; Build instance index: from the store's complete TSV when present, else name-based discovery (~200ms).
  (let [tsv-candidates (when store-path
                         ["resources/instances.tsv" "instances.tsv"
                          (str store-path "/instances.tsv")])
        tsv-path (some (fn [p] (let [f (clojure.java.io/file p)]
                                 (when (.exists f) (.getPath f))))
                       tsv-candidates)
        load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
        build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
        idx (if tsv-path
              (do (when *verbose* (println "Loading instance registry from" tsv-path "..."))
                  (load-tsv tsv-path))
              (build-fn env))]
    (reset! ansatz-instance-index idx)
    (when (resolve 'ansatz.core/synth-cache)
      (reset! @(resolve 'ansatz.core/synth-cache) {}))
    (when *verbose*
      (println "Ansatz:" (.size ^ansatz.kernel.Env @ansatz-env) "declarations loaded,"
               (count idx) "classes indexed"))))

(clojure.core/defn- init!*
  [store-path branch]
  (let [sm (storage/open-store store-path)
        env (storage/load-env sm branch)]
    (setup-env! env store-path)))

(def ^:private bundled-medium-resource "ansatz/init-medium.ndjson.gz")

(clojure.core/defn- bundled-medium-env
  "Replay the bundled medium Init tier (gzipped lean4export NDJSON resource) into an
   env, in TRUST mode (:verify? false — a known-good export, admitted without
   re-checking). nil if the resource isn't on the classpath."
  []
  (when-let [res (clojure.java.io/resource bundled-medium-resource)]
    (let [s (with-open [in (java.util.zip.GZIPInputStream. (clojure.java.io/input-stream res))]
              (slurp in))
          decls (:decls ((requiring-resolve 'ansatz.export.parser/parse-ndjson-string) s))]
      (:env ((requiring-resolve 'ansatz.export.replay/replay) decls :verify? false)))))

(clojure.core/defn- init!-bundled-medium! []
  (if-let [env (bundled-medium-env)]
    (do (setup-env! env nil)
        (println (str "Ansatz: loaded the bundled medium Init tier ("
                      (.size ^ansatz.kernel.Env @ansatz-env) " declarations, TRUST mode).\n"
                      "  For the full Init or Mathlib, build a durable store and call "
                      "(init! \"init\") / (init! \"mathlib\")."))
        :medium)
    (throw (ex-info (str "Bundled medium Init resource not found on the classpath: "
                         bundled-medium-resource " — is ansatz on the classpath as a built jar?")
                    {:resource bundled-medium-resource}))))

(clojure.core/defn load-init!
  "ZERO-CONFIG bootstrap for library users: load Lean `Init` from the export bundled in the jar
   (`resources/ansatz/init-medium.ndjson.gz`, ~3000 decls — Nat/List/Eq/basics), replayed in TRUST
   mode, plus the instance index. Enough to verify basic CIC functions and prove theorems against Init.
   For a full Init or Mathlib store, build one (scripts/setup-*.sh) and use `init!`. Returns the Env."
  []
  (let [res (clojure.java.io/resource "ansatz/init-medium.ndjson.gz")]
    (when-not res
      (throw (ex-info "bundled Init export not on classpath (resources/ansatz/init-medium.ndjson.gz)" {})))
    ;; Stream straight from the (jar) resource: gunzip on the fly, parse the in-memory string.
    ;; No temp file — works on read-only / sandboxed filesystems and GraalVM native-image, and
    ;; identically whether the bundle is a loose classpath file (dev) or inside the jar.
    (let [ndjson (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
                   (slurp in))
          env    (:env (replay/replay (:decls (parser/parse-ndjson-string ndjson)) :verify? false))]
      (reset! ansatz-env env)
      (reset! ansatz-instance-index (instance/build-instance-index env))
      (attrs/load-bundled-attrs!)   ;; inherit Lean's @[simp]/@[csimp]/@[extern] into env extensions
      (matchers/load-bundled-matchers!)  ;; inherit Lean's Match.MatcherInfo (for the `split` tactic)
      (when *verbose* (println "Ansatz: Init loaded —" (.size ^ansatz.kernel.Env @ansatz-env) "declarations"))
      @ansatz-env)))

(clojure.core/defn env [] (or @ansatz-env (throw (ex-info "Call (ansatz/init!) or (ansatz/load-init!) first" {}))))
(clojure.core/defn instance-index [] (or @ansatz-instance-index {}))

(declare synth-cache)

;; Dynamic vars for elaboration context threading
(def ^:dynamic *current-lctx* nil)

(clojure.core/defn- compute-arity
  "Compute the runtime arity of a function type.
   Returns {:arity n :erased k} where n = explicit params, k = erased (implicit/inst) prefix."
  [fn-type]
  (loop [t fn-type explicit 0 erased 0 in-prefix true]
    (if (e/forall? t)
      (let [bi (e/forall-info t)]
        (if (= :default bi)
          (recur (e/forall-body t) (inc explicit) erased false)
          (recur (e/forall-body t) explicit (if in-prefix (inc erased) erased) in-prefix)))
      {:arity explicit :erased erased})))

(clojure.core/defn context
  "Get the current global ProofContext (built from global atoms)."
  []
  (->ProofContext (env) (instance-index) @(resolve 'ansatz.core/synth-cache)))

;; ============================================================
;; Instance resolution (name-based, works with PSS env)
;; ============================================================

(clojure.core/defn resolve-basic-instance
  "Resolve a basic typeclass instance like Add/Mul/Sub/Div for a given type.
   Tries naming conventions: inst{Class}{Type}, {Type}.inst{Class}, etc.
   Returns the Ansatz term for the instance, or nil."
  [env class-str type-name-str type-expr]
  (let [candidates [(str "inst" class-str type-name-str)           ;; instAddNat
                    (str type-name-str ".inst" class-str)          ;; Real.instAdd
                    (str "inst" class-str type-name-str type-name-str) ;; instAddNatNat
                    (str type-name-str ".inst" class-str type-name-str)] ;; Nat.instDivNat
        found (some (fn [n]
                      (when-let [ci (env/lookup env (name/from-string n))]
                        (let [lps (vec (.levelParams ^ConstantInfo ci))]
                          (if (empty? lps)
                            (e/const' (name/from-string n) [])
                            (e/app (e/const' (name/from-string n) (mapv (fn [_] lvl/zero) lps))
                                   type-expr)))))
                    candidates)]
    (or found
        ;; General superclass coercion: try ALL "{Super}.to{Class}" patterns.
        ;; Covers the entire Mathlib hierarchy without manual chains.
        (let [;; Common superclasses (covers algebraic + order + normed hierarchies)
              common-supers
              ["Field" "DivisionRing" "Ring" "CommRing" "Semiring" "CommSemiring"
               "GroupWithZero" "MonoidWithZero"
               "AddCommMonoid" "AddCommGroup" "AddMonoid" "AddGroup" "AddZeroClass"
               "CommMonoid" "CommGroup" "Monoid" "Group" "MulOneClass"
               "MulZeroOneClass" "MulZeroClass"
               "NonUnitalNonAssocSemiring" "NonAssocSemiring"
               "SubtractionMonoid" "SubtractionCommMonoid"
               "NormedField" "NormedCommRing" "NormedRing" "NonUnitalNormedRing"
               "NormedAddCommGroup" "SeminormedAddCommGroup"
               "NormedSpace" "NormedAlgebra" "RCLike"
               "OrderedSemiring" "StrictOrderedSemiring" "IsOrderedRing"
               "LinearOrderedField" "LinearOrderedSemiring"
               "PartialOrder" "Preorder" "LinearOrder"
               "Mul" "Add" "Sub" "Div" "Neg" "SMul"
               "Semigroup" "AddSemigroup" "AddCommMagma" "CommMagma"]
              ;; H-class wrappers: inst{HClass} takes (type, base-inst)
              h-class? (#{"HAdd" "HMul" "HSub" "HDiv" "HSMul" "HPow"} class-str)
              chains (when-not h-class?
                       (keep (fn [super]
                               (let [coercion (str super ".to" class-str)]
                                 (when (env/lookup env (name/from-string coercion))
                                   [super coercion])))
                             common-supers))]
          (or
            ;; H-class wrappers: inst{HClass} type base-inst
           (when h-class?
             (let [inst-name (str "inst" class-str)]
               (when (env/lookup env (name/from-string inst-name))
                 (let [base-class (subs class-str 1)
                       base-inst (resolve-basic-instance env base-class type-name-str type-expr)]
                   (when base-inst
                     (let [lps (vec (.levelParams ^ConstantInfo (env/lookup env (name/from-string inst-name))))]
                       (e/app* (e/const' (name/from-string inst-name)
                                         (mapv (fn [_] lvl/zero) lps))
                               type-expr base-inst)))))))
            ;; Super.toClass coercions
            ;; Walk the coercion's forall telescope, filling each param:
            ;; - Type params → type-expr
            ;; - Inst-implicit → synthesize
            ;; - Explicit (the super-class instance) → super-inst
           (some (fn [[super-class coercion-fn]]
                   (when-let [super-inst (resolve-basic-instance env super-class type-name-str type-expr)]
                     (let [^ConstantInfo ci (env/lookup env (name/from-string coercion-fn))
                           lps (vec (.levelParams ci))
                           ctype (if (seq lps)
                                   (e/instantiate-level-params (.type ci)
                                                               (zipmap lps (repeat lvl/zero)))
                                   (.type ci))]
                        ;; Walk foralls and fill each param
                       (loop [ty ctype
                              term (e/const' (name/from-string coercion-fn)
                                             (mapv (fn [_] lvl/zero) lps))
                              super-used? false]
                         (if-not (e/forall? ty)
                           term  ;; done
                           (let [binfo (e/forall-info ty)
                                 btype (e/forall-type ty)
                                 btype-whnf (try (let [st (tc/mk-tc-state env)]
                                                   (#'tc/cached-whnf st btype))
                                                 (catch Exception _ btype))]
                             (cond
                                ;; Type implicit → use type-expr
                               (and (#{:implicit :strict-implicit} binfo)
                                    (e/sort? btype-whnf))
                               (recur (e/instantiate1 (e/forall-body ty) type-expr)
                                      (e/app term type-expr) super-used?)

                                ;; Inst-implicit OR implicit class instance → synthesize
                               (or (= binfo :inst-implicit)
                                    ;; Implicit that looks like a class (non-Sort type)
                                   (and (#{:implicit :strict-implicit} binfo)
                                        (not (e/sort? btype-whnf))
                                        (e/const? (e/get-app-fn btype))))
                               (if-let [inst (let [synth-fn (requiring-resolve 'ansatz.tactic.instance/synthesize*)]
                                               (try (synth-fn (tc/mk-tc-state env) env (instance-index) btype 0)
                                                    (catch Exception _ nil)))]
                                 (recur (e/instantiate1 (e/forall-body ty) inst)
                                        (e/app term inst) super-used?)
                                 nil)  ;; can't synthesize → fail this chain

                                ;; Explicit → use super-inst (first explicit only)
                               (and (= binfo :default) (not super-used?))
                               (recur (e/instantiate1 (e/forall-body ty) super-inst)
                                      (e/app term super-inst) true)

                                ;; Other → can't fill
                               :else nil)))))))
                 chains))))))

;; ============================================================
;; Auto-elaboration: fill implicit + instance-implicit args
;; ============================================================

(defonce ^:private synth-cache (atom {}))

(clojure.core/defn- try-synthesize-instance
  "Try to synthesize an instance for the given type.
   Cached per goal-type. Uses instance index + synthesis engine,
   falling back to name-based resolution with derivation chains.
   Optional cache-atom overrides the global synth-cache (for ProofContext isolation)."
  ([env goal-type] (try-synthesize-instance env goal-type nil nil))
  ([env goal-type instance-idx] (try-synthesize-instance env goal-type instance-idx nil))
  ([env goal-type instance-idx cache-atom]
   (let [cache (or cache-atom synth-cache)
         ;; ENV-AWARE key: the global synth-cache is `defonce` and survives manual `(reset! ansatz-env …)`
         ;; (only `init!` clears it). Keying by goal-type ALONE meant a `::miss` cached against a SMALLER
         ;; env (e.g. init-medium, which couldn't synthesize an instance) was wrongly reused by a LARGER
         ;; env (init-full, which can) — a deterministic cross-test/proof poison. Include the env identity
         ;; (Env has no value-equality, so identity-hash is its identity; an int, so we don't retain the
         ;; env → no leak). Within one env (one proof) the cache still memoizes.
         ckey [(System/identityHashCode env) goal-type]]
     (if-let [cached (find @cache ckey)]
       (let [v (val cached)] (when-not (= v ::miss) v))
       (let [result (or
      ;; Try full synthesis engine with cached index
                     (try
                       (let [synth-fn (requiring-resolve 'ansatz.tactic.instance/synthesize*)
                             st (tc/mk-tc-state env)]
                         (synth-fn st env (or instance-idx (instance-index)) goal-type 0))
                       (catch Exception _ nil))
      ;; Fallback: name-based resolution with derivation chains
                     (let [[head args] (e/get-app-fn-args goal-type)]
                       (when (and (e/const? head) (seq args))
                         (let [class-name (name/->string (e/const-name head))
                               type-arg (first args)
                               [th _] (when type-arg (e/get-app-fn-args type-arg))
                               type-name (when (e/const? th) (name/->string (e/const-name th)))]
                           (when type-name
                             (resolve-basic-instance env class-name type-name type-arg))))))]
         (swap! cache assoc ckey (or result ::miss))
         result)))))

(clojure.core/defn get-arg-type
  "Get the type of a user argument. Handles bvars (via bvar-types),
   fvars (via *current-lctx*), and general expressions (via TC)."
  [env bvar-types arg]
  (or (when (and bvar-types (e/bvar? arg))
        (get bvar-types (e/bvar-idx arg)))
      (when (and *current-lctx* (e/fvar? arg))
        (:type (get *current-lctx* (e/fvar-id arg))))
      (try (tc/infer-type (tc/mk-tc-state env) arg) (catch Exception _ nil))))

(clojure.core/defn- match-type-args
  "First-order pattern matching of expected type against actual type.
   Solves mvar placeholders by matching constructor heads and arguments.
   Returns a map of mvar-id → value, or nil if matching fails.

   Example: expected = (List (mvar 1)), actual = (List Nat)
            → {1 Nat}"
  [expected actual]
  (cond
    ;; Mvar: solved!
    (e/mvar? expected) {(e/mvar-id expected) actual}
    ;; Both are apps: match head and args
    (and (e/app? expected) (e/app? actual))
    (let [[eh ea] (e/get-app-fn-args expected)
          [ah aa] (e/get-app-fn-args actual)]
      (when (= (count ea) (count aa))
        (let [head-match (match-type-args eh ah)]
          (reduce (fn [acc [e a]]
                    (if acc
                      (let [sub (match-type-args e a)]
                        (when sub (merge acc sub)))
                      nil))
                  (or head-match {})
                  (map vector ea aa)))))
    ;; Both are consts: match if same name
    (and (e/const? expected) (e/const? actual)
         (= (name/->string (e/const-name expected))
            (name/->string (e/const-name actual))))
    {}
    ;; Identical leaves
    (and (e/lit-nat? expected) (e/lit-nat? actual)
         (= (e/lit-nat-val expected) (e/lit-nat-val actual)))
    {}
    ;; Mismatch
    :else nil))

(clojure.core/defn- auto-elaborate
  "Auto-elaborate a function application by inserting implicit and
   instance-implicit arguments. Following Lean 4's App.lean:
   - {implicit} → create mvar placeholder, solve by unifying with explicit arg types
   - [inst-implicit] → synthesize via TC resolution
   - (explicit) → consume next user argument, unify to solve pending mvars
   bvar-types: optional map of bvar-idx → type for inferring types of bound vars."
  [env head-fn fn-type user-args & {:keys [bvar-types] :or {bvar-types nil}}]
  (let [;; First instantiate level params with zero (default heuristic)
        ^ConstantInfo ci (env/lookup env (e/const-name head-fn))
        lparams (when ci (vec (.levelParams ci)))
        level-subst (when (seq lparams) (zipmap lparams (repeat lvl/zero)))
        fn-type (if level-subst
                  (e/instantiate-level-params fn-type level-subst)
                  fn-type)
        next-mvar (atom 0)]
    (loop [f head-fn
           ftype fn-type
           args user-args
           ;; Track unsolved implicit mvars: [{:mvar-id :mvar-expr}]
           pending-implicits []]
      (if (e/forall? ftype)
        (let [binfo (e/forall-info ftype)
              btype (e/forall-type ftype)
              body (e/forall-body ftype)]
          (case binfo
            ;; Explicit parameter: consume next user arg.
            ;; Try to solve pending implicit mvars by unifying expected domain with arg type.
            :default
            (if (seq args)
              (let [arg (first args)
                    ;; If there are pending implicits, try to solve them
                    ;; by matching the expected domain (btype, which contains mvars)
                    ;; against the actual arg type.
                    arg-ty (when (seq pending-implicits)
                             (get-arg-type env bvar-types arg))
                    solutions (when arg-ty
                                (match-type-args btype arg-ty))
                    ;; Apply solutions: substitute solved mvars in f and ftype
                    [f ftype] (if (seq solutions)
                                (reduce (fn [[f ft] [mid val]]
                                          [(extract/replace-mvar f mid val)
                                           (extract/replace-mvar ft mid val)])
                                        [f (e/forall' "_" btype body :default)]
                                        solutions)
                                [f (e/forall' "_" btype body :default)])
                    ;; After substitution, re-extract btype and body
                    btype' (if (e/forall? ftype) (e/forall-type ftype) btype)
                    body' (if (e/forall? ftype) (e/forall-body ftype) body)]
                (recur (e/app f arg)
                       (e/instantiate1 body' arg)
                       (vec (rest args))
                       ;; Clear solved implicits
                       (if (seq solutions)
                         (vec (remove #(contains? solutions (:mvar-id %)) pending-implicits))
                         pending-implicits)))
              ;; No more args — partial application
              f)

            ;; Implicit: create mvar placeholder (Lean 4 style).
            ;; Will be solved later when we see the explicit arg.
            ;; Special case: if the implicit expects a type (Sort u) and the first
            ;; user arg IS a type, use it directly (common pattern: List.nil Nat).
            (:implicit :strict-implicit)
            (let [st (tc/mk-tc-state env)
                  btype-whnf (try (#'tc/cached-whnf st btype) (catch Exception _ btype))
                  ;; Check if first user arg directly fills this implicit
                  direct-fill
                  (when (and (e/sort? btype-whnf) (seq args))
                    (let [arg (first args)
                          arg-ty (get-arg-type env bvar-types arg)]
                      (when (and arg-ty (e/sort? arg-ty))
                        ;; arg IS a type → use directly as the implicit value
                        arg)))]
              (if direct-fill
                ;; Direct fill: consume the user arg for this implicit
                (recur (e/app f direct-fill)
                       (e/instantiate1 body direct-fill)
                       (vec (rest args))
                       pending-implicits)
                ;; Defer: create mvar, solve later
                (let [mid (swap! next-mvar inc)
                      mvar-expr (e/mvar mid)]
                  (recur (e/app f mvar-expr)
                         (e/instantiate1 body mvar-expr)
                         args
                         (conj pending-implicits {:mvar-id mid :mvar-expr mvar-expr :type btype})))))

            ;; Instance-implicit: synthesize via TC.
            ;; If the type contains unsolved mvars, defer until they're solved.
            :inst-implicit
            (let [inst (try-synthesize-instance env btype)]
              (if inst
                (recur (e/app f inst)
                       (e/instantiate1 body inst)
                       args
                       pending-implicits)
                ;; Can't synthesize — leave as placeholder
                (recur (e/app f btype)
                       (e/instantiate1 body btype)
                       args
                       pending-implicits)))))
        ;; Not a forall — apply remaining user args directly
        (reduce e/app f args)))))

(clojure.core/defn- resolve-hop-instance
  "Build the full H-operator instance: instHOp α (basic-inst).
   hop-name: 'HAdd', 'HMul', etc.
   basic-class: 'Add', 'Mul', etc."
  [env hop-name basic-class type-name-str type-expr]
  (when-let [basic-inst (resolve-basic-instance env basic-class type-name-str type-expr)]
    (let [inst-hop-name (str "inst" hop-name)]
      (when-let [ci (env/lookup env (name/from-string inst-hop-name))]
        (e/app* (e/const' (name/from-string inst-hop-name) [lvl/zero])
                type-expr basic-inst)))))

(clojure.core/defn- build-binop
  "Build a binary operator application generically.
   Resolves instances automatically for the given type."
  [env op-name hop-name basic-class type-name-str type-expr a b]
  (let [inst (resolve-hop-instance env hop-name basic-class type-name-str type-expr)]
    (if inst
      (e/app* (e/const' (name/from-string op-name) [lvl/zero lvl/zero lvl/zero])
              type-expr type-expr type-expr inst a b)
      (throw (ex-info (str "No " basic-class " instance for " type-name-str) {})))))

;; ============================================================
;; Runtime helpers (the legacy bvar compiler that lived here was retired in P5)
;; ============================================================

(declare parse-params build-telescope-fvar)

(clojure.core/defn rt-sizeof
  "Runtime sizeOf mirroring the kernel sizeOf_spec equations: a Nat is its own size;
   a (runtime, seq-encoded) list is 1 (nil) plus, per element, 1 + its size."
  [v]
  (cond
    (integer? v) v
    (or (nil? v) (sequential? v)) (reduce (fn [acc e] (+ acc 1 (rt-sizeof e))) 1 v)
    :else 1))

;; Type context for outer-scope variables — used by match handler to
;; register fvars in the tc's local context. Maps symbol → Expr (type).
;; *scope-types* and *current-lctx* are defined at the top of the file.

  ;; ── The bvar-scoped legacy elaborator (sexp->ansatz, build-telescope, compile-let*,
;; cond->if, scope-bvar-types, infer-value-type) was retired in P5 of the elaborator
;; unification: ansatz.surface.elaborate (fvar/metavar, lean4-shaped) is the single
;; elaborator for bodies, signatures, measures, theorem statements and tactic arguments.

;; Codegen (nary-op, tagged-inductive?, builtin-app/value, ansatz->clj) lives in ansatz.codegen.
;; Re-export so internal call sites + a/ansatz->clj (the wandler-facing codegen entry) keep resolving.
(def ansatz->clj codegen/ansatz->clj)

;; ============================================================
;; Tactic runner
;; ============================================================

(declare run-tactic)

;; ============================================================
;; Extensible registries (Lean 4's @[tactic], @[simproc], elab_rules)
;; ============================================================

(clojure.core/defn register-tactic!
  "Register a custom tactic. The function receives (ps args) and must return a new proof state.

   Example:
     (a/register-tactic! 'my-tac
       (fn [ps args]
         (let [goal (ansatz.tactic.proof/current-goal ps)
               st   (ansatz.kernel.tc/mk-tc-state (a/env))]
           ;; Full access to kernel: tc/infer-type, tc/cached-whnf, tc/is-def-eq
           ;; Full access to proof state: proof/current-goal, proof/assign-mvar
           ...)))

   Then use in proofs:
     (a/theorem foo [...] prop (my-tac arg1 arg2))"
  [name f]
  (swap! tactic-registry assoc name f))

(clojure.core/defn register-elaborator!
  "Register a custom surface form (lean4 macro_rules-shaped): f receives the argument FORMS
   and returns a replacement surface form, which the elaborator then elaborates — syntax →
   syntax, composing with every surface feature.

   Example:
     (a/register-elaborator! 'double (fn [args] (list '+ (first args) (first args))))
     (a/defn ^Nat f [^Nat x] (double x))"
  [name f]
  (swap! ingest/elaborator-registry assoc name f))

(clojure.core/defn register-term-elaborator!
  "Register a custom TERM elaborator (lean4's elab_rules): (fn [est args] -> kernel Expr),
   with elaborator access via ansatz.surface.api (elab / arg-type) -- for type-directed
   forms that the form->form register-elaborator! cannot express."
  [sym f]
  ((requiring-resolve 'ansatz.surface.api/register-term-elaborator!) sym f))

(clojure.core/defn register-simproc!
  "Register a persistent simplification procedure for simp.

   The function receives (st expr) where st is a tc-state and expr is the
   expression to simplify. Return {:expr simplified :proof eq-proof} or nil.

   Example:
     (a/register-simproc! 'my-domain/eval
       (fn [st expr]
         (when (my-domain-expr? expr)
           {:expr (evaluate expr) :proof (build-eq-proof expr)})))"
  [_name f]
  (swap! simproc-registry conj f))

(clojure.core/defn- simp-lemma-args
  "Resolve a surface `(simp …)` argument list into simp's lemma vector. A bare symbol stays a
   symbol (env name resolution / @[simp]-set merge). A COMPOUND form — `(WSemiring.mul_zero m)`,
   `(h x)` — is elaborated in the current goal's context into a proof TERM (an ansatz.kernel.Expr),
   which simp/simp accepts directly (it infers the term's type and extracts its rewrite rule). This
   is what lets a bundled typeclass axiom be applied to its instance and fed to simp thinly —
   `simp [(WSemiring.mul_add m) …]` — the way Lean's `simp [m.mul_add]` does."
  [ps args]
  (let [;; Accept both `(simp a b)` (flat) and `(simp [a b])` (a single vector) — the latter is the
        ;; common surface form; without flattening, the whole vector would be treated as one arg and
        ;; (mis)elaborated as a term, throwing (and under all_goals that throw is swallowed → the
        ;; tactic silently no-ops).
        args (if (and (= 1 (count args)) (vector? (first args))) (first args) args)
        g (proof/current-goal ps)]
    (mapv (fn [a]
            (cond
              ;; A bare symbol is a lemma/def NAME (resolved by simp). This is the ONE canonical
              ;; way to name things in the tactic DSL.
              (symbol? a) a
              ;; A string is NOT a name — the surface elaborator turns it into a `String` literal
              ;; (a value), which is useless as a simp lemma and silently makes simp a no-op. This
              ;; is a footgun (esp. for programmatically-built tactics that stringify const names):
              ;; reject it loudly so the mistake fails fast. Write the name as a symbol.
              (string? a)
              (throw (ex-info (str "simp: lemma argument must be a name (symbol) or a proof term, "
                                   "got the string " (pr-str a) " — write it as a symbol, e.g. "
                                   "(simp [" a "]) not (simp [" (pr-str a) "]).")
                              {:kind :tactic-error :arg a}))
              ;; Anything else (a compound form) elaborates to a proof term in the goal context.
              :else (elab/elaborate-in-context (:env ps) (:lctx g) a)))
          args)))

(clojure.core/defn- elab-apply-arg
  "Resolve an `apply`/`solve_by_elim` lemma argument to a kernel term, returning [ps' term].
   A bare symbol that names a LOCAL HYPOTHESIS resolves to that fvar first (locals shadow globals,
   as in Lean's apply/solve_by_elim) — so e.g. a quantified hypothesis `h : ∀x, f x ~ g x` can be
   passed and applied. Otherwise: bare symbol → `@`-explicit elaboration (no implicit insertion,
   like Lean's elabTermForApply); compound form → elaborate in context. If a bare symbol is a
   universe-polymorphic const whose universe is not pinned standalone (e.g. List.Perm.nil :
   @List.Perm.{u} α [] []), elaboration throws — so we mint fresh Level.mvars for its levelParams
   and let apply-tac's meta-isDefEq solve them against the goal (Lean's forallMetaTelescope +
   isDefEq). Mirrors Apply.lean."
  [ps lctx arg]
  (let [hyp-fid (when (symbol? arg)
                  (reduce (fn [best [id d]]
                            (if (and (= :local (:tag d)) (= (str arg) (:name d))
                                     (or (nil? best) (> (long id) (long best))))
                              id best))
                          nil lctx))]
    (if hyp-fid
      [ps (e/fvar hyp-fid)]
      (let [arg' (if (symbol? arg) (symbol (str "@" arg)) arg)]
        (try [ps (elab/elaborate-in-context (:env ps) lctx arg')]
             (catch Throwable ex
               (if (and (symbol? arg)
                        (clojure.string/includes? (str (.getMessage ex)) "universe level"))
                 (let [ci (env/lookup (:env ps) (name/from-string (str arg)))
                       lparams (vec (.levelParams ^ansatz.kernel.ConstantInfo ci))
                       [ps' ids] (reduce (fn [[p acc] _]
                                           (let [[p' i] (proof/alloc-id p)] [p' (conj acc i)]))
                                         [ps []] lparams)]
                   [ps' (e/const' (name/from-string (str arg)) (mapv lvl/mvar ids))])
                 (throw ex))))))))

(clojure.core/defn- do-rewrite-one
  "A SINGLE rewrite rule: a local hypothesis (by name), an env lemma (∀-quantified, instantiated by
   matching), or an applied Eq term. `reverse?` rewrites right-to-left."
  [ps reverse? spec]
  (let [g (proof/current-goal ps)
        hyp-fid (when (symbol? spec)
                  (reduce (fn [best [id d]]
                            (if (and (= (str spec) (:name d))
                                     (or (nil? best) (> (long id) (long best))))
                              id best))
                          nil (:lctx g)))
        term (if hyp-fid
               (e/fvar hyp-fid)
               ;; env lemma: elaborate @-explicit so implicits stay ∀-bound (rewrite-lemma
               ;; instantiates ALL params by matching); applied form elaborates as-is.
               (elab/elaborate-in-context
                (:env ps) (:lctx g)
                (if (symbol? spec) (symbol (str "@" spec)) spec)))]
    (basic/rewrite-lemma ps term reverse?)))

(clojure.core/defn- do-rewrite
  "Lean's `rewrite` (NOT `rw`): rewrite the goal by a local hypothesis (by name), an env lemma
   (∀-quantified, instantiated by matching), or an applied Eq term. Faithful to Lean's bracketed
   `rewrite [r1, r2, …]`: a VECTOR argument is a SEQUENCE of rewrite rules applied left-to-right, each
   optionally prefixed `←`/`<-` for a right-to-left rewrite (Lean's `rw [← h, g]`). A bare/applied
   form (or a leading `←`/`<-`) is a single rule. NOTE: the vector must NOT be elaborated as a term —
   `[lemma]` is a list literal whose element-universe level mvar is never constrained, so it would
   surface as an 'unsolved universe level' error. Does NOT close the goal — that's `rw`'s `try rfl`."
  [ps args]
  (if (vector? (first args))
    ;; rw [r1, r2, …] — sequential rewrites, per-element ←/<- for reverse
    (loop [ps ps, toks (seq (first args))]
      (if (empty? toks)
        ps
        (let [rev? (boolean (#{'<- '←} (first toks)))
              spec (if rev? (second toks) (first toks))
              rest-toks (if rev? (drop 2 toks) (rest toks))]
          (recur (do-rewrite-one ps rev? spec) rest-toks))))
    (let [reverse? (boolean (#{'<- '←} (first args)))
          spec (if reverse? (second args) (first args))]
      (do-rewrite-one ps reverse? spec))))

(def ^:private builtin-tactics
  {'rfl        (fn [ps _] (basic/rfl ps))
   'assumption (fn [ps _] (basic/assumption ps))
   'constructor (fn [ps _] (basic/constructor ps))
   'exfalso   (fn [ps _] (basic/exfalso ps))
   'contradiction (fn [ps _] (basic/contradiction ps))
   'left      (fn [ps _] (basic/left ps))
   'right     (fn [ps _] (basic/right ps))
   'exact?    (fn [ps _] (basic/exact? ps))
   'exact     (fn [ps args]
                ;; (exact <term>) — close the goal with an explicit proof term, elaborated in the
                ;; goal's local context (hypotheses in scope). The companion to exact? (auto-search).
                ;; BIDIRECTIONAL (faithful to Lean's `exact`): the goal type is the EXPECTED type, so a
                ;; partially-applied citation whose implicits aren't pinned by its explicit args alone
                ;; (e.g. `List.map_congr_left h` — f/g/l implicit) gets them solved by unifying the
                ;; lemma's conclusion against the goal, instead of surfacing "unsolved metavariables".
                (let [g (proof/current-goal ps)
                      term (try (elab/elaborate-in-context (:env ps) (:lctx g) (first args) (:type g))
                                ;; fall back to expectation-free elaboration if the expected-type unify
                                ;; rejects a def-eq-but-not-syntactic match the kernel would still accept.
                                (catch Throwable _
                                  (elab/elaborate-in-context (:env ps) (:lctx g) (first args))))]
                  (basic/exact ps term)))
   'omega     (fn [ps _] (omega/omega ps))
   'ac_rfl    (fn [ps _] (ac/ac-rfl ps))
   'trans     (fn [ps args]
                ;; (trans mid h1 h2) — transitivity: a ≤ mid, mid ≤ c → a ≤ c
                ;; Builds: @le_trans Real inst a mid c h1 h2
                (let [g (proof/current-goal ps)
                      lctx (:lctx g)
                      ;; Get α from goal: LE.le α inst a c
                      [_ goal-args] (e/get-app-fn-args (:type g))
                      alpha (first goal-args)
                      inst (second goal-args)
                      a-val (nth goal-args 2)
                      c-val (nth goal-args 3)
                      ;; Parse args
                      mid (elab/elaborate-in-context (:env ps) lctx (first args))
                      h1-term (elab/elaborate-in-context (:env ps) lctx (second args))
                      h2-term (elab/elaborate-in-context (:env ps) lctx (nth args 2))
                      ;; Build le_trans.{0} α inst a mid c h1 h2
                      ;; le_trans : {α} [Preorder α] {a b c : α} → a ≤ b → b ≤ c → a ≤ c
                      preorder-inst (try-synthesize-instance (:env ps)
                                                             (e/app (e/const' (name/from-string "Preorder") [lvl/zero]) alpha)
                                                             (:instance-index ps))
                      term (e/app* (e/const' (name/from-string "le_trans") [lvl/zero])
                                   alpha (or preorder-inst inst)
                                   a-val mid c-val h1-term h2-term)]
                  (basic/apply-tac ps term)))
   'have      (fn [ps args]
                ;; (have name type)        — introduce `name : type` as a new subgoal to prove, then
                ;;                           continue the body with `name` in scope (Lean `have h : T`).
                ;; (have name type proof)  — discharge that subgoal immediately with `proof` (Lean
                ;;                           `have h : T := proof`); leaves only the body goal.
                (let [hyp-name (str (first args))
                      g (proof/current-goal ps)
                      hyp-type (elab/elaborate-in-context (:env ps) (:lctx g) (second args))
                      ps' (basic/have-tac ps hyp-name hyp-type)]
                  (if (>= (count args) 3)
                    ;; have-tac made the type-subgoal the current goal (sub1 first); close it with the
                    ;; elaborated proof term (in the original context), leaving the body goal current.
                    (let [g1 (proof/current-goal ps')
                          proof-term (elab/elaborate-in-context (:env ps') (:lctx g1) (nth args 2))]
                      (basic/exact ps' proof-term))
                    ps')))
   ;; Lean 4 `simp only [...]` / `simp_all only [...]`: a leading `only` token strips the default
   ;; @[simp] corpus, using ONLY the given lemmas (+ reflexive-closer builtins). See simp/simp opts.
   'simp      (fn [ps args]
                (let [only? (= 'only (first args))
                      args  (if only? (rest args) args)]
                  (cond
                    only?      (simp/simp ps (simp-lemma-args ps args) {:only? true})
                    (seq args) (simp/simp ps (simp-lemma-args ps args))
                    :else      (simp/simp ps))))
   'simp_all  (fn [ps args]
                (let [only? (= 'only (first args))
                      args  (if only? (rest args) args)]
                  (cond
                    only?      (simp/simp-all ps (simp-lemma-args ps args) {:only? true})
                    (seq args) (simp/simp-all ps (simp-lemma-args ps args))
                    :else      (simp/simp-all ps))))
   'dsimp     (fn [ps _args] (simp/dsimp ps))
   'intro     (fn [ps args] (if (seq args) (basic/intros ps (mapv str args)) (basic/intro ps)))
   'intros    (fn [ps args] (basic/intros ps (mapv str args)))
   'apply     (fn [ps args]
                (let [g (proof/current-goal ps)
                      [ps' term] (elab-apply-arg ps (:lctx g) (first args))]
                  (basic/apply-tac ps' term)))
   ;; Lean 4 `funext` tactic (Init/NotationExtra.lean): a macro over `apply funext; intro`. Proves a
   ;; function-equality goal `f = g` by function extensionality (∀x, f x = g x → f = g):
   ;;   (funext)        => repeat (apply funext; intro)        — peel all function binders
   ;;   (funext x)      => apply funext; intro x
   ;;   (funext x y …)  => apply funext; intro x; funext y …
   'funext    (fn [ps args]
                (if (seq args)
                  (reduce (fn [ps x] (basic/intros (basic/apply-funext ps) [(str x)])) ps args)
                  (loop [ps ps i 0]
                    (if (>= i 64) ps
                        (if-let [ps' (try (basic/intro (basic/apply-funext ps)) (catch Throwable _ nil))]
                          (recur ps' (inc i)) ps)))))
   ;; Lean 4's two tactics, faithfully split (Init/Tactics.lean:606 — `rw` ≡ `rewrite; try rfl`):
   ;;   (rewrite h) / (rewrite <- lemma) / (rewrite (lemma a b)) — rewrite ONLY, leaves the goal.
   ;;   (rw …)                                                   — rewrite, then `try (rfl)` to close.
   'rewrite   (fn [ps args] (do-rewrite ps args))
   'rw        (fn [ps args]
                ;; `rw` = `rewrite` then a cheap reflexivity attempt (Lean appends `try (with_reducible
                ;; rfl)`). The `try` is essential: a non-refl residual goal survives. (basic/rfl uses
                ;; full is-def-eq vs Lean's reducible-only — a benign superset under `try`: it can only
                ;; close MORE refl goals, never reject.)
                (let [ps' (do-rewrite ps args)]
                  (try (basic/rfl ps') (catch Throwable _ ps'))))
   'cases     (fn [ps args]
                ;; (cases h)      — case-split on hypothesis `h` (by name)
                ;; (cases hp e)   — faithful `cases hp : e`: substitute Bool discriminant `e`,
                ;;                  adding `hp : e = true/false` per branch (Lean's idiom)
                (let [rest-args (rest args)]
                  (if (seq rest-args)
                    (let [hname (str (first args))
                          g (proof/current-goal ps)
                          cond-expr (elab/elaborate-in-context (:env ps) (:lctx g) (first rest-args))]
                      (basic/cases-eq ps cond-expr hname))
                    (let [nm (str (first args))
                          fid (reduce (fn [best [id d]]
                                        (if (and (= nm (:name d))
                                                 (or (nil? best) (> (long id) (long best))))
                                          id best))
                                      nil (:lctx (proof/current-goal ps)))]
                      (basic/cases ps fid)))))
   'generalize (fn [ps args]
                 ;; (generalize x h e) — Lean's `generalize h : e = x`: abstract term `e` in the goal
                 ;; as fresh var `x` (+ hyp `h : e = x`), so `cases`/`induction` can split a NESTED
                 ;; scrutinee (the RAWREC case).
                 (let [xname (str (first args))
                       hname (str (second args))
                       g (proof/current-goal ps)
                       e-expr (elab/elaborate-in-context (:env ps) (:lctx g) (nth args 2))]
                   (basic/generalize ps e-expr xname hname)))
   'induction (fn [ps args]
                ;; (induction x) or (induction x generalizing acc …) — Lean's `generalizing`:
                ;; revert the named hyps INTO the goal first (so the induction motive becomes
                ;; ∀ acc…, P x and the IH is the ∀-quantified `∀ acc…, P tail` foldl proofs need),
                ;; do induction on x, then re-intro acc… in every resulting case.
                (let [find-fid (fn [ps nm]
                                 (reduce (fn [best [id d]]
                                           (if (and (= nm (:name d))
                                                    (or (nil? best) (> (long id) (long best))))
                                             id best))
                                         nil (:lctx (proof/current-goal ps))))
                      gen? (= 'generalizing (second args))
                      gen-syms (when gen? (vec (drop 2 args)))
                      ;; revert innermost-last (reverse order) so re-intro restores original order
                      ps (reduce (fn [ps g] (basic/revert ps (find-fid ps (str g))))
                                 ps (reverse gen-syms))
                      ps (basic/induction ps (find-fid ps (str (first args))))]
                  (if (seq gen-syms)
                    (basic/all-goals ps (fn [ps'] (basic/intros ps' (mapv str gen-syms))))
                    ps)))
   'whnf      (fn [ps _args] (basic/whnf-goal ps))
   'unfold    (fn [ps args]
                (basic/unfold-in-goal ps (str (first args))))
   'by_cases  (fn [ps args]
                (let [g (proof/current-goal ps)
                      cond-expr (elab/elaborate-in-context (:env ps) (:lctx g) (first args))]
                  (basic/by-cases ps cond-expr)))
   ;; Combinators — these receive inner tactic forms as s-expressions
   'try       (fn [ps args]
                ;; (try (tactic args)) — try the inner tactic; on failure, leave state unchanged
                (basic/try-tac ps (fn [ps'] (reduce run-tactic ps' args))))
   'all_goals (fn [ps args]
                ;; (all_goals (tactic args)) — apply inner tactic to every open goal
                (basic/all-goals ps (fn [ps'] (reduce run-tactic ps' args))))
   'first     (fn [ps args]
                ;; (first (tac1 args) (tac2 args) ...) — try each tactic in order
                (apply basic/first-tac ps
                       (map (fn [tac-form] (fn [ps'] (run-tactic ps' tac-form))) args)))
   'and_then  (fn [ps args]
                ;; (and_then (tac1 args) (tac2 args) ...) — run tac1, then apply remaining tactics to all goals
                ;; Semantics of Lean 4's <;> operator
                (let [ps' (run-tactic ps (first args))]
                  (basic/all-goals ps' (fn [ps''] (reduce run-tactic ps'' (rest args))))))
   ;; Decision procedures
   'decide    (fn [ps _args]
                (let [f (requiring-resolve 'ansatz.tactic.decide/decide)] (f ps)))
   'norm_num  (fn [ps _args]
                (let [f (requiring-resolve 'ansatz.tactic.norm-num/norm-num)] (f ps)))
   'linarith  (fn [ps _args]
                (let [f (requiring-resolve 'ansatz.tactic.linarith/linarith)] (f ps)))
   'ring      (fn [ps _args]
                (let [f (requiring-resolve 'ansatz.tactic.ring/ring)] (f ps)))
   ;; Inequality automation
   'positivity (fn [ps _args]
                 (let [f (requiring-resolve 'ansatz.tactic.positivity/positivity)] (f ps)))
   'gcongr    (fn [ps _args]
                (let [f (requiring-resolve 'ansatz.tactic.gcongr/gcongr)] (f ps)))
   'grind     (fn [ps args]
                (let [f (requiring-resolve 'ansatz.tactic.grind/grind)]
                  (f ps (vec (map str args)))))
   'solve_by_elim (fn [ps args]
                    ;; Lean 4 `solve_by_elim [lemmas]`: backtracking apply over the hypotheses PLUS
                    ;; the given lemma set. We resolve each lemma arg to a TERM the way `apply` does
                    ;; (bare symbol → `@`-explicit elaboration; compound form → elaborate in context),
                    ;; then hand the term vector to basic/solve-by-elim as extra apply-candidates.
                    ;; Closes e.g. the `induction h` (List.Perm) cases by applying the Perm
                    ;; constructors (nil/cons/swap/trans) + assumption on the IHs.
                    (let [g (proof/current-goal ps)
                          flat (if (and (= 1 (count args)) (vector? (first args))) (first args) args)
                          [ps' lemmas] (reduce (fn [[p acc] a]
                                                 (let [[p' t] (elab-apply-arg p (:lctx g) a)]
                                                   [p' (conj acc t)]))
                                               [ps []] flat)]
                      (if (seq lemmas)
                        (basic/solve-by-elim ps' 6 lemmas)
                        (basic/solve-by-elim ps'))))
   'split_ifs (fn [ps _args] (basic/split-ifs ps))
   'split     (fn [ps _args] (basic/split-tac ps))
   'revert    (fn [ps args]
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/revert ps fid)))
   'subst     (fn [ps args]
                ;; (subst h) — Lean's `subst h`: given `h : x = e` / `e = x`, eliminate the variable.
                (let [nm (str (first args))
                      fid (some (fn [[id d]] (when (= nm (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/subst ps fid)))
   'subst_vars (fn [ps _args]
                 ;; (subst_vars) — Lean's `subst_vars`: subst every variable-equality hypothesis.
                 (basic/subst-vars ps))})

;; Initialize registry with built-in tactics
(when (empty? @tactic-registry)
  (reset! tactic-registry builtin-tactics))

(clojure.core/defn run-tactic [ps tac]
  (let [registry @tactic-registry]
    (if (symbol? tac)
      (if-let [f (get registry tac)] (f ps nil)
              (throw (ex-info (str "Unknown tactic: " tac) {:available (keys registry)})))
      (let [[name & args] tac]
        (if-let [f (get registry name)] (f ps (vec args))
                (throw (ex-info (str "Unknown tactic: " name) {:available (keys registry)})))))))

;; ============================================================
;; Param parsing — handles :- and :inst markers
;; ============================================================

;; Re-exported from ansatz.surface.ingest (shared, breaks the core↔elaborate cycle).
(def binder-type ingest/binder-type)
(def metadata-params? ingest/metadata-params?)
(def parse-params ingest/parse-params)

;; ============================================================
;; Well-Founded Recursion → ansatz.wf
;; ============================================================
;; The lean4-faithful WellFounded.Nat.fix encoding, GuessLex measure inference, guard-aware decrease
;; checking and sizeOf derivation live in ansatz.wf now. Re-export the entry points core's
;; dispatcher / macros call (define-verified-wf, elab-signature, wf-guess-measure, wf-derive-sizeof!).
(def define-verified-wf wf/define-verified-wf)
(def elab-signature wf/elab-signature)
(def wf-guess-measure wf/wf-guess-measure)
(def wf-derive-sizeof! wf/wf-derive-sizeof!)

;; ============================================================
;; Partial / Foreign definers (the recursion-ladder fallbacks)
;; ============================================================

(clojure.core/defn define-partial
  "Define a PARTIAL (trusted, opaque) function — the recursion ladder's lenient fallback, for recursion
   we can't or won't prove total. The kernel gets an AXIOM at the function's type: trusted, NOT verified,
   and never usable in proofs (data-only). The runtime is the original recursive Clojure body — self-calls
   resolve to the def'd var at call time. Mark with ^:partial. Mirrors Lean's `partial def`."
  [fn-name params ret-type-form body-form]
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)
        ;; function type  ∀ params → ret  (same construction as define-verified)
        {ret-ansatz :ret-ansatz type-ansatz :type-ansatz} (elab-signature env pairs ret-type-form)
        cname (name/from-string (str fn-name))
        ;; trusted axiom at the type; also the self-reference used to elaborate the body for codegen
        ax (env/mk-axiom cname [] type-ansatz)
        tmp-env (env/add-constant (env/fork env) ax)
        ;; Compile body fvar-first (consistent with define-verified/-wf), for codegen only.
        body-ansatz (binding [surface-match/*use-cases-on?* true]
                      (build-telescope-fvar tmp-env pairs ret-type-form body-form))]
    ;; install the trusted axiom + arity in the real env (NOT a verified def — opaque, no body)
    (swap! ansatz-env env/add-constant ax)
    (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
    (println "⚠ partial:" fn-name "— trusted (axiom at its type), NOT verified; not usable in proofs")
    ;; codegen the recursive body; self-calls compile to (fn-name …) and resolve at call time
    (let [clj-form (ansatz->clj @ansatz-env body-ansatz [])
          clj-fn (if (<= n 1)
                   (eval clj-form)
                   (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) (vec pairs))
                         curried-call (reduce (fn [f s] (list f s))
                                              (list clj-form (first param-syms)) (rest param-syms))]
                     (eval
                      `(fn
                         (~[(first param-syms)]
                          ~(if (= n 2)
                             `(fn [~(second param-syms)] ~curried-call)
                             (reduce (fn [body s] `(fn [~s] ~body))
                                     curried-call (reverse (rest param-syms)))))
                         (~param-syms ~curried-call)))))]
      clj-fn)))

(clojure.core/defn define-foreign
  "Declare a TRUSTED FOREIGN function: an arbitrary Clojure fn asserted at the given
   kernel type (installed as an AXIOM — trusted, not verified, never usable in proofs).
   Unlike `define-partial`, the body is NOT elaborated — the raw Clojure fn IS the runtime.
   In a verified body the foreign name resolves as a constant of its asserted type, so the
   optimizer reasons PARAMETRICALLY around it (fusion/relational laws hold for ANY function),
   and codegen lowers it like any user fn (FAP via the arity registry → calls the def'd var).
   The asserted type is the entire trust boundary — the gradual escape hatch / typed FFI hole."
  [fn-name params ret-type-form]
  (let [env (env)
        pairs (parse-params params)
        {type-ansatz :type-ansatz} (elab-signature env pairs ret-type-form)
        cname (name/from-string (str fn-name))
        ax (env/mk-axiom cname [] type-ansatz)]
    (swap! ansatz-env env/add-constant ax)
    (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
    (println "⚠ foreign:" fn-name "— trusted Clojure fn asserted at its type, NOT verified")
    :foreign))

;; ============================================================
;; Public API
;; ============================================================

(clojure.core/defn- build-telescope-fvar
  "fvar-first body elaboration via surface/elaborate: params become fvars in the
   lctx, the body elaborates with full inference (instances/levels/match), then the
   fvars are abstracted back into the lambda telescope — same shape as build-telescope."
  [env pairs ret-type-form body-form]
  (let [n (count pairs)
        fids (mapv inc (range n))
        ;; Elaborate param types in an ACCUMULATING context (a dependent telescope), so a later
        ;; binder's type can reference an earlier binder — e.g. `[S :- Type, m :- (WAddMonoid S)]`
        ;; resolves S. (elab-signature already does this for the ∀-type; the body-lambda must match,
        ;; else polymorphic/dependent signatures fail with "Unknown constant: S".)
        ptypes (loop [i 0 lctx {} acc []]
                 (if (= i n) acc
                     (let [p (nth pairs i)
                           pt (elab/elaborate-in-context env lctx (second p))]
                       (recur (inc i)
                              (assoc lctx (nth fids i) {:name (str (first p)) :type pt :tag :local})
                              (conj acc pt)))))
        ;; A Subtype-typed param (e.g. a malli [:int {:min k}] refinement) registers with an
        ;; :as-term coercion: body references elaborate as `Subtype.val T P p`, so refined
        ;; params are used directly as their carrier (the refinement is erased at runtime;
        ;; the .property remains available to proof machinery from the binder type).
        subtype-val (fn [fid pt]
                      (let [[h as] (e/get-app-fn-args pt)]
                        (when (and (e/const? h) (= "Subtype" (name/->string (e/const-name h)))
                                   (= 2 (count as)))
                          (e/app* (e/const' (name/from-string "Subtype.val")
                                            (vec (e/const-levels h)))
                                  (nth as 0) (nth as 1) (e/fvar fid)))))
        lctx (into {} (map (fn [fid p pt]
                             [fid (cond-> {:name (str (first p)) :type pt :tag :local}
                                    (subtype-val fid pt) (assoc :as-term (subtype-val fid pt)))])
                           fids pairs ptypes))
        body-expr (elab/elaborate-in-context env lctx body-form)
        ;; abstract-many maps V[k] → bvar (len-1-k) (last → bvar 0), so pass fids in
        ;; param order (fids[0]=outermost param → highest bvar). Do NOT reverse.
        body-bvar (e/abstract-many body-expr fids)]
    (loop [i (dec n) acc body-bvar]
      (if (< i 0) acc
          (let [[pn _ binfo] (nth pairs i)]
            ;; A dependent param type may reference earlier binders' fvars; abstract those
            ;; (fids[0..i-1]) into bvars so the lambda binding type is closed (mirrors
            ;; elab-signature's mkForallFVars), else the type leaks "Unknown free variable".
            (recur (dec i) (e/lam (str pn)
                                  (e/abstract-many (nth ptypes i) (subvec fids 0 i))
                                  acc (or binfo :default))))))))

(clojure.core/defn- mentions-const?
  "Does expr reference the constant named nm anywhere?"
  [expr nm]
  (case (e/tag expr)
    :const  (= (e/const-name expr) nm)
    :app    (or (mentions-const? (e/app-fn expr) nm) (mentions-const? (e/app-arg expr) nm))
    :lam    (or (mentions-const? (e/lam-type expr) nm) (mentions-const? (e/lam-body expr) nm))
    :forall (or (mentions-const? (e/forall-type expr) nm) (mentions-const? (e/forall-body expr) nm))
    :let    (or (mentions-const? (e/let-type expr) nm) (mentions-const? (e/let-value expr) nm)
                (mentions-const? (e/let-body expr) nm))
    :proj   (mentions-const? (e/proj-struct expr) nm)
    false))

(declare define-verified-impl)
(declare define-verified)

(clojure.core/defn- hoist-loops!
  "Desugar general (loop [x e1 y e2 …] body) forms in an a/defn body into synthesized local
   WF helper functions: the loop becomes (helper e1 e2 … encl…), `recur` becomes a self-call,
   and the helper goes through the SAME verified pipeline — structural recursion, auto-measure
   (single Nat or lexicographic GuessLex), kernel-enforced WellFounded.fix. Loop vars and the
   loop result are assumed Nat (the WF machinery is Nat-gated); enclosing fn params referenced
   by the body are closure-converted into extra constant helper params. Innermost loops hoist
   first, so each `recur` belongs to its own loop. If a helper cannot be defined (non-Nat loop,
   unprovable termination), the loop form is left intact for the legacy counting-shape
   elaboration (elab-loop) — strictly more programs verify, none regress."
  [fn-name param-syms body-form]
  (letfn [(subst-recur [form helper-sym extra-args]
            ;; rewrite (recur a …) → (helper a … extra…); inner loops were already hoisted,
            ;; so every remaining recur belongs to the current loop
            (cond
              (and (seq? form) (= 'recur (first form)))
              (list* helper-sym (concat (map #(subst-recur % helper-sym extra-args) (rest form))
                                        extra-args))
              (seq? form) (apply list (map #(subst-recur % helper-sym extra-args) form))
              (vector? form) (mapv #(subst-recur % helper-sym extra-args) form)
              :else form))
          (occurs? [sym form]
            (cond (= sym form) true
                  (or (seq? form) (vector? form)) (boolean (some #(occurs? sym %) form))
                  :else false))
          (walk [form]
            (cond
              (and (seq? form) (= 'loop (first form)) (vector? (second form)))
              (let [bindings (second form)
                    lbody0 (nth form 2)
                    lbody (walk lbody0)                       ; hoist inner loops first
                    loop-vars (vec (take-nth 2 bindings))
                    inits (mapv walk (take-nth 2 (rest bindings)))
                    encl (vec (for [p param-syms
                                    :when (and (not (some #{p} loop-vars)) (occurs? p lbody))]
                                p))
                    helper-sym (gensym (str fn-name "-loop"))
                    helper-params (vec (mapcat (fn [v] [v :- 'Nat]) (concat loop-vars encl)))
                    helper-body (subst-recur lbody helper-sym encl)]
                (try
                  (let [f (define-verified helper-sym helper-params 'Nat helper-body)]
                    (intern *ns* helper-sym f)
                    (list* helper-sym (concat inits encl)))
                  (catch Throwable t
                    (when *verbose*
                      (println (str "  loop hoisting unavailable (" (.getMessage t)
                                    ") — falling back to counting-shape elaboration")))
                    form)))
              (seq? form) (apply list (map walk form))
              (vector? form) (mapv walk form)
              :else form))]
    (walk body-form)))

(clojure.core/defn define-verified
  "Define a verified function. Auto-detects structural recursion; if the recursion is not
   structural, tries lean4's GuessLex (single Nat measure, then lexicographic pairs) and
   redirects to well-founded recursion when a decreasing measure is found. General loop/recur
   forms are hoisted into synthesized WF helper functions first. Returns the compiled Clojure fn."
  [fn-name params ret-type-form body-form]
  (let [body-form (hoist-loops! fn-name (mapv first (parse-params params)) body-form)]
    (try
      (define-verified-impl fn-name params ret-type-form body-form)
      (catch clojure.lang.ExceptionInfo e
        (if (= ::redirect-wf (:kind (ex-data e)))
          (define-verified-wf fn-name params ret-type-form body-form (:measure (ex-data e)))
          (throw e))))))

(clojure.core/defn- define-verified-impl
  "Structural-recursion path. Throws {:kind ::redirect-wf :measure m} when recursion is
   non-structural but a WF measure was synthesized (handled by define-verified)."
  [fn-name params ret-type-form body-form]
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)
        cname (name/from-string (str fn-name))
        ;; Build type ∀ params → ret-type up front (the self-axiom below needs it).
        ;; `_` return type = INFER it from the body (non-recursive fns only — e.g. a
        ;; select-keys terminal whose synthesized projection-record type is unnameable):
        ;; elaborate the body once without a self-axiom and read its type.
        {ret-ansatz :ret-ansatz type-ansatz :type-ansatz}
        (if (= '_ ret-type-form)
          ;; a surface elaborator may SYNTHESIZE constants into the global env mid-flight
          ;; (select-keys' projection record) — the snapshot the elaboration started with
          ;; can't see them, so retry once against the refreshed env (synthesis is idempotent)
          (let [build (fn [e] (build-telescope-fvar e pairs nil body-form))
                body-lam (try (build env) (catch Exception _ (build @ansatz-env)))
                tc0 (doto (ansatz.kernel.TypeChecker. ^ansatz.kernel.Env @ansatz-env)
                      (.setFuel (long config/*default-fuel*)))
                ft (.inferType tc0 body-lam)
                ret (loop [t ft, k n]
                      (if (zero? k) t (recur (e/forall-body t) (dec k))))]
            {:ret-ansatz ret :type-ansatz ft})
          (elab-signature env pairs ret-type-form))
        ;; the inference pass may have EXTENDED the global env (e.g. select-keys
        ;; synthesizing its projection record) — re-read it for the real elaboration
        env (if (= '_ ret-type-form) @ansatz-env env)
        ;; Elaborate the body fvar-first (Lean-faithful, metavar-complete) — the SOLE path
        ;; (the bvar fallback was retired). A tmp self-axiom lets a NATURAL recursive call
        ;; (isort tl) resolve during elaboration; build-minor-premise rewrites structural
        ;; self-calls on a bare recursive field to that field's IH (Lean's affordance — no
        ;; manual ih_<field>). Non-structural leftovers still reference the axiom → check-constant
        ;; rejects them (the user adds :termination-by / ^:partial). Existing ih_<field> bodies
        ;; keep working. Elaboration failures otherwise surface honestly.
        tmp-env (env/add-constant (env/fork env) (env/mk-axiom cname [] type-ansatz))
        ;; *self-params* = the param fvar-ids build-telescope-fvar uses (1..n), so multi-arg
        ;; self-calls (add k n) are recognised: recursive field at the matched position, the
        ;; other args the unchanged params.
        ;; The structural self-call→IH rewrite is only SOUND when the match is the entire
        ;; function body (then the recursor's IH is literally `f field`). For any other shape
        ;; (if-wrapped, let-wrapped, nested) the IH is a different fold — those self-calls stay
        ;; as the axiom and route to the well-founded path below.
        top-match? (and (seq? body-form) (= 'match (first body-form)))
        body-ansatz (binding [surface-match/*self-name* (when top-match? cname)
                              surface-match/*self-params* (when top-match? (vec (range 1 (inc n))))]
                      (build-telescope-fvar tmp-env pairs ret-type-form body-form))
        ;; If a self-call survived as the axiom, structural auto-detection didn't apply — give an
        ;; actionable error (the recursion lane prompt) instead of a cryptic kernel "unknown constant".
        _ (when (mentions-const? body-ansatz cname)
            ;; Not structural. Try lean4's GuessLex (single Nat measure) — if a measure makes
            ;; every recursive call provably decrease, redirect to well-founded recursion;
            ;; otherwise give the actionable recursion-lane prompt.
            (if-let [m (wf-guess-measure pairs body-form fn-name n)]
              (throw (ex-info "auto-measure WF" {:kind ::redirect-wf :measure m}))
              (throw (ex-info
                      (str "Cannot auto-verify recursive function `" fn-name "`: its recursive call isn't "
                           "structurally decreasing on a parameter, and no Nat measure (single or "
                           "lexicographic pair) was found to be decreasing. Add `:termination-by <measure>` "
                           "(a vector for lexicographic, e.g. [m n]) for well-founded recursion, or "
                           "`^:partial` for trusted (unverified) recursion.")
                      {:fn fn-name :kind :non-structural-recursion}))))
        ;; Type-check on the REAL env (no axiom — every self-call must have become an IH).
        tc (ansatz.kernel.TypeChecker. env)
        _ (.inferType tc body-ansatz)
        ci (env/mk-def cname [] type-ansatz body-ansatz)
        _ (swap! ansatz-env env/check-constant ci)
        ;; Register arity for Clojure compilation (FAP/PAP dispatch)
        _ (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
        ;; Generate equation theorems for simp (Lean 4's getEqnsFor? pattern).
        ;; Uses fvar-based open/close: create fvars for params+fields,
        ;; WHNF-reduce with fvars, then abstract-many to get correct bvars.
        _ (try
            (let [env' @ansatz-env
                  ;; Find the outermost recursor in the body
                  peeled (loop [e body-ansatz i 0]
                           (if (and (< i n) (e/lam? e))
                             (recur (e/lam-body e) (inc i))
                             e))
                  [rec-head _] (e/get-app-fn-args peeled)]
              (when (and (e/const? rec-head)
                         (.endsWith ^String (name/->string (e/const-name rec-head)) ".rec"))
                (let [^ConstantInfo rci (env/lookup env' (e/const-name rec-head))
                      np (.numParams rci)
                      ind-name-str (subs (name/->string (e/const-name rec-head)) 0
                                         (- (count (name/->string (e/const-name rec-head))) 4))
                      ^ConstantInfo ind-ci (env/lookup env' (name/from-string ind-name-str))
                      ctor-names (.ctors ind-ci)
                      ;; Determine discriminant position from recursor major premise.
                      ;; The major premise is the last rec arg and is a bvar.
                      ;; bvar(k) in the peeled body = param at position (n - 1 - k).
                      rec-args-raw (vec (e/get-app-args peeled))
                      major-arg (peek rec-args-raw)
                      discr-pos (if (e/bvar? major-arg)
                                  (- n 1 (e/bvar-idx major-arg))
                                  (dec n))  ;; fallback: last param
                      n-non-discr (dec n)
                      ;; positions of the non-discriminant params (the fixed prefix + any
                      ;; trailing carried params), in order — used to map a loose param-bvar
                      ;; in the peeled body back to the eq-gen's param fvar.
                      non-discr-indices (vec (remove #{discr-pos} (range n)))]
                  (doseq [i (range (count ctor-names))]
                    (try
                      (let [ctor-name (nth ctor-names i)
                            ^ConstantInfo ctor-ci (env/lookup env' ctor-name)
                            nf (.numFields ctor-ci)
                            cnp (.numParams ctor-ci)
                            ;; Create fvars for non-discriminant params and ctor fields
                            fv-base 8200000
                            param-fvids (mapv #(+ fv-base %) (range n-non-discr))
                            field-fvids (mapv #(+ fv-base n-non-discr %) (range nf))
                            all-fvids (vec (concat param-fvids field-fvids))
                            param-fvars (mapv e/fvar param-fvids)
                            field-fvars (mapv e/fvar field-fvids)
                            ;; Inductive type params (e.g. `S` in `List S`) = the args applied to the
                            ;; inductive in the DISCRIMINANT's type. Derive the discriminant's type by
                            ;; peeling the fn type telescope, instantiating each earlier binder with
                            ;; its eq-gen param fvar — for a polymorphic fn this resolves `S` to the S
                            ;; param fvar (no loose bvar, no placeholder fvar leak into field-types).
                            fn-type (.type ^ConstantInfo (env/lookup env' cname))
                            discr-type (loop [t fn-type p 0]
                                         (cond (not (e/forall? t)) t
                                               (= p discr-pos) (e/forall-type t)
                                               :else (recur (e/instantiate1 (e/forall-body t)
                                                                            (nth param-fvars (.indexOf ^java.util.List non-discr-indices p)))
                                                            (inc p))))
                            ind-type-params (vec (take np (e/get-app-args discr-type)))
                            ;; Constructor levels
                            ctor-levels (let [clps (vec (.levelParams ctor-ci))
                                              rlps (vec (.levelParams rci))
                                              rlevs (e/const-levels rec-head)]
                                          (mapv (fn [clp]
                                                  (let [idx (.indexOf rlps clp)]
                                                    (if (>= idx 0) (nth rlevs idx) lvl/zero)))
                                                clps))
                            ;; Build ctor-app and LHS with fvars.
                            ;; Place ctor-app at the discriminant position, other params around it.
                            ctor-app (reduce e/app (e/const' ctor-name ctor-levels)
                                             (concat ind-type-params field-fvars))
                            lhs-args (let [pv (vec param-fvars)]
                                       (into (into (subvec pv 0 discr-pos) [ctor-app])
                                             (subvec pv discr-pos)))
                            lhs (reduce e/app (e/const' cname []) lhs-args)
                            ;; Get field types by peeling ctor type (with levels instantiated)
                            ctor-type-inst (let [clps (vec (.levelParams ctor-ci))
                                                 subst (zipmap clps ctor-levels)]
                                             (if (seq subst)
                                               (e/instantiate-level-params (.type ctor-ci) subst)
                                               (.type ctor-ci)))
                            field-types (loop [t ctor-type-inst skip cnp j 0 acc []]
                                          (if (or (not (e/forall? t)) (>= j nf)) acc
                                              (if (pos? skip)
                                                (let [sub (if (< (- cnp skip) (count ind-type-params))
                                                            (nth ind-type-params (- cnp skip))
                                                            (e/sort' lvl/zero))]
                                                  (recur (e/instantiate1 (e/forall-body t) sub) (dec skip) j acc))
                                                (recur (e/instantiate1 (e/forall-body t) (nth field-fvars j))
                                                       0 (inc j) (conj acc (e/forall-type t))))))
                            ;; Non-discriminant param types, for the WHNF lctx. Peel the FUNCTION's
                            ;; type telescope instantiating each binder with its eq-gen repr (param
                            ;; fvar, or the ctor-app at the discriminant) — this yields the correctly
                            ;; DEPENDENT types (e.g. m : WAddMonoid S with S the eq-gen's S fvar).
                            ;; Re-elaborating the surface form standalone fails on polymorphic /
                            ;; instance params (`(WAddMonoid S)` → "Unknown constant: S").
                            reprs (mapv (fn [p]
                                          (if (= p discr-pos) ctor-app
                                              (nth param-fvars (.indexOf ^java.util.List non-discr-indices p))))
                                        (range n))
                            param-types (loop [t fn-type p 0 acc []]
                                          (if (or (>= p n) (not (e/forall? t))) acc
                                              (recur (e/instantiate1 (e/forall-body t) (nth reprs p))
                                                     (inc p)
                                                     (if (= p discr-pos) acc (conj acc (e/forall-type t))))))
                            ;; Return type in THIS eq-gen's param fvars (peel all binders). The
                            ;; elaborator's :ret-ansatz references elab-signature's own param fvars
                            ;; (wf-fix-fresh ids) which are NOT abstracted — for a polymorphic fn
                            ;; (ret = S) that fvar would leak into the equation as "Unknown free
                            ;; variable". Reconstruct ret over param-fvars so it abstracts cleanly.
                            ret-eq (loop [t fn-type p 0]
                                     (if (or (>= p n) (not (e/forall? t))) t
                                         (recur (e/instantiate1 (e/forall-body t) (nth reprs p)) (inc p))))
                            st' (reduce (fn [s [fid nm tp]]
                                          (update s :lctx red/lctx-add-local fid nm tp))
                                        (tc/mk-tc-state env')
                                        (concat (map vector param-fvids
                                                     (map #(str (first (nth (vec pairs) (nth non-discr-indices %)))) (range n-non-discr))
                                                     param-types)
                                                (map vector field-fvids
                                                     (map #(str "f" %) (range nf))
                                                     field-types)))
                            ;; Build RHS using RESTRICTED WHNF (Lean 4: withReducible).
                            ;; Use transparency mode 0 (reducible) with only the function
                            ;; being defined + its recursor in the allow set.
                            ;; This reduces the match/recursor (iota) but NOT + or other fns.
                            rhs-raw
                            (let [tc-eq (ansatz.kernel.TypeChecker. env')
                                  allow-set (java.util.HashSet.)
                                  rec-name-obj (e/const-name rec-head)]
                              ;; Allow ONLY the function being defined to be delta-unfolded.
                              ;; Iota reduction (recursor matching) is always allowed — it's
                              ;; not delta. This means: llen unfolds → List.rec exposed →
                              ;; iota selects cons branch → result has 1 + llen tail.
                              ;; The + is NOT unfolded because it's not in the allow set.
                              (.add allow-set cname)
                              (.setFuel tc-eq 5000000)
                              (.setTransparency tc-eq 0)
                              (.setDeltaAllowSet tc-eq allow-set)
                              ;; Add fvars to lctx
                              (doseq [[fid nm tp] (concat
                                                   (map vector param-fvids
                                                        (map #(str (first (nth (vec pairs) (nth non-discr-indices %)))) (range n-non-discr))
                                                        param-types)
                                                   (map vector field-fvids
                                                        (map #(str "f" %) (range nf))
                                                        field-types))]
                                (.addLocal tc-eq (long fid) (str nm) tp))
                              ;; WHNF with restricted transparency
                              (.whnf (.getReducer tc-eq) lhs))
                            ;; Replace recursive recursor patterns with function calls.
                            ;; Lean 4: equation theorems show f(args) not raw recursors.
                            ;; The rec parameter in the cons-case gets substituted during
                            ;; iota reduction with the full recursor applied to the tail.
                            ;; We compute that exact expression and replace all occurrences
                            ;; with f(tail_fvar). This is Lean 4's replaceRecApps equivalent.
                            rec-args (vec (e/get-app-args peeled))
                            ;; The rec value = full recursor applied to the tail fvar.
                            ;; It's the same as the function body but with tail fvar as scrutinee.
                            ;; Identify which field is the recursive one (type matches the inductive)
                            rec-field-idx (first (keep-indexed
                                                  (fn [j ft]
                                                    (let [[fh _] (e/get-app-fn-args ft)]
                                                      (when (and (e/const? fh)
                                                                 (= (name/->string (e/const-name fh)) ind-name-str))
                                                        j)))
                                                  field-types))
                            rhs-clean
                            (if rec-field-idx
                              (try
                              ;; Build the rec-value by instantiating the body with the
                              ;; ACTUAL constructor args (including l=ctor-app), then
                              ;; replacing the major premise with tail-fvar.
                              ;; Lean 4: replaceRecApps finds .brecOn/.below references.
                              ;; Our approach: the rec-value has l=ctor-app baked in
                              ;; (from the outer beta reduction), matching the RHS.
                                (let [tail-fvar (nth field-fvars rec-field-idx)
                                    ;; Instantiate body with params + ctor-app for the discriminant
                                      ^ConstantInfo fn-ci (env/lookup env' cname)
                                      fn-body (.value fn-ci)
                                    ;; Instantiate outer lambdas with param fvars and ctor-app
                                    ;; Args in original parameter order: insert ctor-app at discr-pos
                                      inst-args (let [pv (vec param-fvars)]
                                                  (into (into (subvec pv 0 discr-pos) [ctor-app])
                                                        (subvec pv discr-pos)))
                                      inst-body (loop [b fn-body fvs inst-args]
                                                  (if (empty? fvs) b
                                                      (recur (e/instantiate1 (e/lam-body b) (first fvs))
                                                             (rest fvs))))
                                    ;; inst-body is the rec application with all params substituted
                                    ;; Replace major premise (last arg) with tail-fvar
                                      [inst-head inst-args] (e/get-app-fn-args inst-body)
                                      rec-val (reduce e/app inst-head
                                                      (conj (vec (butlast inst-args)) tail-fvar))
                                    ;; The function call to replace with
                                    ;; Place tail-fvar at discriminant position
                                      f-call-args (let [pv (vec param-fvars)]
                                                    (into (into (subvec pv 0 discr-pos) [tail-fvar])
                                                          (subvec pv discr-pos)))
                                      f-call (reduce e/app (e/const' cname []) f-call-args)
                                    ;; Find and replace rec-val with f-call in the RHS
                                      replace-fn (fn replace-rv [expr]
                                                   (if (= expr rec-val)
                                                     f-call
                                                     (case (e/tag expr)
                                                       :app (let [nf (replace-rv (e/app-fn expr))
                                                                  na (replace-rv (e/app-arg expr))]
                                                              (if (and (identical? nf (e/app-fn expr))
                                                                       (identical? na (e/app-arg expr)))
                                                                expr (e/app nf na)))
                                                       :lam (let [nb (replace-rv (e/lam-body expr))]
                                                              (if (identical? nb (e/lam-body expr))
                                                                expr (e/lam (e/lam-name expr) (e/lam-type expr)
                                                                            nb (e/lam-info expr))))
                                                       expr)))]
                                  (replace-fn rhs-raw))
                                (catch Exception _ rhs-raw))
                              rhs-raw)
                            ;; Create auxiliary matcher definitions for stuck inner recursors
                            ;; (Lean 4: each match expression becomes a named matcher).
                            ;; Replace stuck recursors in the RHS with calls to auxiliaries.
                            ;; Each auxiliary gets its own equation theorems.
                            rhs-with-aux
                            (try
                              (let [aux-counter (atom 0)
                                    create-aux (fn create-aux [rhs depth]
                                                 (if (> depth 3) rhs
                                                     (let [[h as] (e/get-app-fn-args rhs)]
                                                       (if (and (e/const? h)
                                                                (.endsWith ^String (name/->string (e/const-name h)) ".rec")
                                                                (seq as) (e/fvar? (last as)))
                                            ;; Found a stuck recursor — create auxiliary definition
                                                         (let [scrut-fvar-id (e/fvar-id (last as))
                                                  ;; Collect all fvars actually used in this stuck expression.
                                                  ;; This ensures deeper recursive calls capture the right context.
                                                               expr-fvars (let [acc (atom #{})]
                                                                            (letfn [(walk [e]
                                                                                      (when (e/has-fvar-flag e)
                                                                                        (case (e/tag e)
                                                                                          :fvar (swap! acc conj (e/fvar-id e))
                                                                                          :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                                                                                          :lam (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                                                                                          :forall (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                                                                                          nil)))]
                                                                              (walk rhs))
                                                                            @acc)
                                                               all-fv-ids (vec (remove #{scrut-fvar-id}
                                                                                       (sort (disj expr-fvars scrut-fvar-id))))
                                                  ;; The auxiliary takes: all free vars + the scrutinee as last param
                                                               aux-fvids (conj all-fv-ids scrut-fvar-id)
                                                               aux-n (swap! aux-counter inc)
                                                               aux-name-str (str fn-name "._match_" aux-n)
                                                               aux-cname (name/from-string aux-name-str)
                                                  ;; Build aux body: abstract fvars from rhs, wrap in lambdas
                                                               aux-body-abs (e/abstract-many rhs aux-fvids)
                                                               aux-fvar-types (mapv (fn [fid]
                                                                                      (let [d (get-in st' [:lctx fid])]
                                                                                        (or (:type d) (e/sort' lvl/zero))))
                                                                                    aux-fvids)
                                                               aux-body (loop [j (dec (count aux-fvids)) body aux-body-abs]
                                                                          (if (< j 0) body
                                                                              (let [fid (nth aux-fvids j)
                                                                                    ft (nth aux-fvar-types j)
                                                                                    nm (or (:name (get-in st' [:lctx fid])) (str "x" j))]
                                                                                (recur (dec j) (e/lam nm ft body :default)))))
                                                  ;; Infer aux type from body
                                                               aux-type (try
                                                                          (let [tc-aux (ansatz.kernel.TypeChecker. @ansatz-env)]
                                                                            (.setFuel tc-aux (int config/*default-fuel*))
                                                                            (.inferType tc-aux aux-body))
                                                                          (catch Exception _ nil))]
                                                           (if-not aux-type
                                                             rhs  ;; fallback: return original stuck expr
                                                             (do ;; Register the auxiliary definition
                                                               (swap! ansatz-env env/check-constant
                                                                      (env/mk-def aux-cname [] aux-type aux-body))
                                                ;; Generate equation theorems for the auxiliary
                                                ;; (Use a simple approach: the aux matches on its last param)
                                                               (try
                                                                 (let [irci (env/lookup @ansatz-env (e/const-name h))
                                                                       iind-str (let [s (name/->string (e/const-name h))]
                                                                                  (subs s 0 (- (count s) 4)))
                                                                       iind-ci (env/lookup @ansatz-env (name/from-string iind-str))
                                                                       ictors (.ctors iind-ci) inp (.numParams irci)
                                                                       iparams (vec (take inp as))
                                                                       ilevels (e/const-levels h)
                                                                       n-aux (count aux-fvids)]
                                                                   (doseq [ci-idx (range (count ictors))]
                                                                     (try
                                                                       (let [icn (nth ictors ci-idx)
                                                                             ^ConstantInfo icci (env/lookup @ansatz-env icn)
                                                                             inf (.numFields icci) icnp (.numParams icci)
                                                              ;; Create fvars for ctor fields
                                                                             cf-base (+ fv-base 5000000 (* aux-n 10000) (* ci-idx 100))
                                                                             cf-fvids (mapv #(+ cf-base %) (range inf))
                                                                             cf-fvars (mapv e/fvar cf-fvids)
                                                              ;; Ctor field types
                                                                             ict-sub (zipmap (vec (.levelParams icci)) (vec (rest ilevels)))
                                                                             ict-inst (if (seq ict-sub) (e/instantiate-level-params (.type icci) ict-sub) (.type icci))
                                                                             cf-types (loop [t ict-inst sk icnp j 0 acc []]
                                                                                        (if (or (not (e/forall? t)) (>= j inf)) acc
                                                                                            (if (pos? sk)
                                                                                              (recur (e/instantiate1 (e/forall-body t)
                                                                                                                     (if (< (- icnp sk) (count iparams))
                                                                                                                       (nth iparams (- icnp sk)) (e/sort' lvl/zero)))
                                                                                                     (dec sk) j acc)
                                                                                              (recur (e/instantiate1 (e/forall-body t) (nth cf-fvars j))
                                                                                                     0 (inc j) (conj acc (e/forall-type t))))))
                                                              ;; Build ctor application
                                                                             ica (reduce e/app (e/const' icn (vec (rest ilevels)))
                                                                                         (concat iparams cf-fvars))
                                                              ;; LHS: aux(params..., ctor-app)
                                                                             aux-lhs (reduce e/app (e/const' aux-cname [])
                                                                                             (concat (mapv e/fvar all-fv-ids) [ica]))
                                                              ;; RHS: WHNF of aux applied to concrete ctor.
                                                              ;; Use CURRENT env (includes aux def) for TC state.
                                                                             st-cf (reduce (fn [s [fid nm tp]]
                                                                                             (update s :lctx red/lctx-add-local fid nm tp))
                                                                                           (assoc (tc/mk-tc-state @ansatz-env) :lctx (:lctx st'))
                                                                                           (map vector cf-fvids
                                                                                                (map #(str "cf" %) (range inf)) cf-types))
                                                                             aux-rhs-raw (#'tc/cached-whnf st-cf aux-lhs)
                                                              ;; Recursively replace stuck recursors in the aux RHS
                                                                             aux-rhs (create-aux aux-rhs-raw (inc depth))
                                                              ;; Build equation: ∀ params fields, aux(params, ctor) = rhs
                                                                             eq-body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                                                                             ret-ansatz aux-lhs aux-rhs)
                                                                             abs-eq (e/abstract-many eq-body (vec (concat param-fvids field-fvids all-fv-ids cf-fvids)))
                                                              ;; Wait — this is getting complex. Let me simplify.
                                                              ;; Just register the equation with Eq.refl proof.
                                                                             all-eq-fvids (vec (distinct (concat all-fv-ids cf-fvids)))
                                                                             all-eq-types (vec (concat (mapv (fn [fid] (or (:type (get-in st-cf [:lctx fid])) (e/sort' lvl/zero))) all-fv-ids)
                                                                                                       cf-types))
                                                                             abs-eq2 (e/abstract-many eq-body all-eq-fvids)
                                                                             full-eq-type (loop [j (dec (count all-eq-fvids)) body abs-eq2]
                                                                                            (if (< j 0) body
                                                                                                (recur (dec j) (e/forall' (str "p" j) (nth all-eq-types j) body :default))))
                                                                             rfl-pf (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                                                            ret-ansatz aux-lhs)
                                                                             abs-pf (e/abstract-many rfl-pf all-eq-fvids)
                                                                             full-pf (loop [j (dec (count all-eq-fvids)) body abs-pf]
                                                                                       (if (< j 0) body
                                                                                           (recur (dec j) (e/lam (str "p" j) (nth all-eq-types j) body :default))))
                                                                             eqn-nm (name/from-string (str aux-name-str ".eq_" (inc ci-idx)))]
                                                          ;; Verify and register
                                                                         (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                                                           (.setFuel tc-v (int config/*default-fuel*))
                                                                           (.inferType tc-v full-pf)
                                                                           (swap! ansatz-env env/check-constant (env/mk-thm eqn-nm [] full-eq-type full-pf))
                                                                           (when *verbose* (println (str "  ✓ " aux-name-str ".eq_" (inc ci-idx))))))
                                                                       (catch Exception ex
                                                                         (when *verbose*
                                                                           (when *verbose*
                                                                             (println (str "  ⚠ " aux-name-str ".eq_" (inc ci-idx) " skipped: " (.getMessage ex)))))))))
                                                                 (catch Exception ex
                                                                   (when *verbose*
                                                                     (println "  aux gen for" aux-name-str "FAILED:" (.getMessage ex)))))
                                                ;; Return call to the auxiliary instead of the stuck recursor
                                                               (reduce e/app (e/const' aux-cname []) (mapv e/fvar aux-fvids)))))
                                            ;; No stuck recursor at top — recurse into sub-expressions
                                                         (if (e/app? rhs)
                                                           (let [f (create-aux (e/app-fn rhs) depth)
                                                                 a (create-aux (e/app-arg rhs) depth)]
                                                             (if (and (identical? f (e/app-fn rhs)) (identical? a (e/app-arg rhs)))
                                                               rhs (e/app f a)))
                                                           rhs)))))]
                                (create-aux rhs-clean 0))
                              (catch Exception _ rhs-clean))
                            ;; Split inner stuck recursors (Lean 4: mkEqnTypes splitMatch?).
                            ;; KEEP the general equation (matches opaque args via star-key)
                            ;; AND add split variants (match concrete constructors).
                            split-equations
                            (try
                              (let [split-counter (atom 0)]
                                (letfn [(find-stuck [expr]
                                          (let [[h as] (e/get-app-fn-args expr)]
                                            (cond
                                              (and (e/const? h)
                                                   (.endsWith ^String (name/->string (e/const-name h)) ".rec")
                                                   (seq as) (e/fvar? (last as)))
                                              {:rec-head h :rec-args (vec as) :scrut-fvar (e/fvar-id (last as))}
                                              (e/app? expr)
                                              (or (find-stuck (e/app-fn expr)) (find-stuck (e/app-arg expr)))
                                              :else nil)))
                                        (split-rec [st rhs the-lhs xfvids xtypes sfx depth]
                                          (if (> depth 2) nil
                                              (when-let [{:keys [rec-head rec-args scrut-fvar]} (find-stuck rhs)]
                                                (let [irci (env/lookup env' (e/const-name rec-head))
                                                      iind-str (let [s (name/->string (e/const-name rec-head))]
                                                                 (subs s 0 (- (count s) 4)))
                                                      iind-ci (env/lookup env' (name/from-string iind-str))
                                                      ictors (.ctors iind-ci) inp (.numParams irci)
                                                      iparams (vec (take inp rec-args))
                                                      ilevels (e/const-levels rec-head)]
                                                  (vec (mapcat
                                                        (fn [ci-idx]
                                                          (try
                                                            (let [icn (nth ictors ci-idx)
                                                                  ^ConstantInfo icci (env/lookup env' icn)
                                                                  inf (.numFields icci) icnp (.numParams icci)
                                                                  base (+ fv-base n-non-discr nf (count xfvids)
                                                                          (* ci-idx 100) (* depth 1000))
                                                                  iffids (mapv #(+ base %) (range inf))
                                                                  iffvars (mapv e/fvar iffids)
                                                                  ict-sub (zipmap (vec (.levelParams icci)) (vec (rest ilevels)))
                                                                  ict-inst (let [raw (.type icci)]
                                                                             (if (seq ict-sub) (e/instantiate-level-params raw ict-sub) raw))
                                                                  iftypes (loop [t ict-inst sk icnp j 0 acc []]
                                                                            (if (or (not (e/forall? t)) (>= j inf)) acc
                                                                                (if (pos? sk)
                                                                                  (recur (e/instantiate1 (e/forall-body t)
                                                                                                         (if (< (- icnp sk) (count iparams))
                                                                                                           (nth iparams (- icnp sk)) (e/sort' lvl/zero)))
                                                                                         (dec sk) j acc)
                                                                                  (recur (e/instantiate1 (e/forall-body t) (nth iffvars j))
                                                                                         0 (inc j) (conj acc (e/forall-type t))))))
                                                                  ica (reduce e/app (e/const' icn (vec (rest ilevels)))
                                                                              (concat iparams iffvars))
                                                                  rhs' (e/instantiate1 (e/abstract1 rhs scrut-fvar) ica)
                                                                  lhs' (e/instantiate1 (e/abstract1 the-lhs scrut-fvar) ica)
                                                                  st' (reduce (fn [s [fid nm tp]]
                                                                                (update s :lctx red/lctx-add-local fid nm tp))
                                                                              st (map vector iffids
                                                                                      (map #(str "g" %) (range inf)) iftypes))
                                                                  rhs-r (#'tc/cached-whnf st' rhs')]
                                                           ;; Recurse for deeper splits
                                                              (or (split-rec st' rhs-r lhs' (vec (concat xfvids iffids))
                                                                             (vec (concat xtypes iftypes))
                                                                             (+ (* sfx 10) (inc ci-idx)) (inc depth))
                                                               ;; Leaf: use flat sequential numbering (Lean 4 style)
                                                                  (let [n (swap! split-counter inc)]
                                                                    [{:rhs rhs-r :lhs lhs' :extra-fvids (vec (concat xfvids iffids))
                                                                      :extra-types (vec (concat xtypes iftypes))
                                                                      :suffix (str "s" n)}])))
                                                            (catch Exception _ nil)))
                                                        (range (count ictors))))))))]
                                  (split-rec st' rhs-clean lhs [] [] 0 0)))
                              (catch Exception _ nil))
                            ;; Following Lean 4 (mkEqnTypes/splitMatch?): when leaf-level
                            ;; split equations exist, use ONLY them — each has a concrete
                            ;; constructor pattern. Falls back to general equation only
                            ;; when no splits exist (e.g., Bool inner match).
                            equations (if (seq split-equations)
                                        (vec split-equations)
                                        [{:rhs rhs-clean :condition nil :suffix nil}])]
                        ;; Build and register each equation using abstract-many
                        (doseq [[_ {:keys [rhs lhs extra-fvids extra-types condition suffix]
                                    :or {lhs lhs extra-fvids [] extra-types []}}]
                                (map-indexed vector equations)]
                          (let [;; Collect fvars actually used in LHS and RHS.
                                ;; Split equations may have "phantom" field fvars replaced
                                ;; by inner constructors. Exclude these (Lean 4 style).
                                used-fvars (let [acc (atom #{})]
                                             (letfn [(walk [e]
                                                       (when (e/has-fvar-flag e)
                                                         (case (e/tag e)
                                                           :fvar (swap! acc conj (e/fvar-id e))
                                                           :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                                                           :lam (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                                                           :forall (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                                                           nil)))]
                                               (walk lhs) (walk rhs))
                                             @acc)
                                all-fv-pairs (filterv (fn [[fid _]] (contains? used-fvars fid))
                                                      (map vector
                                                           (concat field-fvids extra-fvids)
                                                           (concat field-types extra-types)))
                                all-fvids (mapv first all-fv-pairs)
                                all-ftypes (mapv second all-fv-pairs)
                                all-nf (count all-fvids)
                                ;; Eq ret_type lhs rhs (all with fvars)
                                eq-body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                                ret-eq lhs rhs)
                                eq-body (if condition (e/arrow condition eq-body) eq-body)
                                abstracted-type
                                (e/abstract-many eq-body (vec (concat param-fvids all-fvids)))
                                ;; Wrap in foralls: all fields then params (right to left). A binder
                                ;; TYPE may depend on earlier binders (a polymorphic field `head : S`,
                                ;; an instance param `m : WAddMonoid S`); abstract those earlier fvars
                                ;; out of each binder type — params are outermost, then fields — so the
                                ;; telescope is well-scoped (else S leaks as "Unknown free variable").
                                full-type (loop [j (dec all-nf) body abstracted-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                                  (e/abstract-many (nth all-ftypes j)
                                                                                   (vec (concat param-fvids (subvec all-fvids 0 j))))
                                                                  body :default))))
                                full-type (loop [j (dec n-non-discr) body full-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                                  (e/abstract-many (nth param-types j) (subvec (vec param-fvids) 0 j))
                                                                  body :default))))
                                ;; Proof: rfl (with fvars), then abstract
                                rfl-proof (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                  ret-eq lhs)
                                proof-body (if condition (e/lam "h" condition rfl-proof :default) rfl-proof)
                                abstracted-proof (e/abstract-many proof-body
                                                                  (vec (concat param-fvids all-fvids)))
                                full-proof (loop [j (dec all-nf) body abstracted-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                               (e/abstract-many (nth all-ftypes j)
                                                                                (vec (concat param-fvids (subvec all-fvids 0 j))))
                                                               body :default))))
                                full-proof (loop [j (dec n-non-discr) body full-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                               (e/abstract-many (nth param-types j) (subvec (vec param-fvids) 0 j))
                                                               body :default))))
                                eqn-name (name/from-string (str fn-name ".eq_" (inc i) (or suffix "")))]
                            (try
                              (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                (.setFuel tc-v (int config/*default-fuel*))
                                (.inferType tc-v full-proof)
                                (swap! ansatz-env env/check-constant (env/mk-thm eqn-name [] full-type full-proof))
                                (when *verbose* (println (str "  ✓ " fn-name ".eq_" (inc i) (or suffix "")))))
                              (catch Exception e
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "skipped:" (.getMessage e))))))))
                      (catch Exception e
                        (when *verbose* (println "  eq" (inc i) "gen failed:" (.getMessage e)))))))))
            (catch Exception ex
              (when *verbose* (println "  eq-gen outer:" (.getMessage ex)))))
        ;; Optimizer seam: a runtime (wandler) may rewrite the body to a kernel-EQUAL, faster term
        ;; just for codegen — the original stays the proven definition in the env. The hook
        ;; receives (env name term) so the runtime can key its explain/plan reports.
        runtime-body (if-let [opt @optimize-hook]
                       (or (opt @ansatz-env (str fn-name) body-ansatz) body-ansatz)
                       body-ansatz)
        ;; Compile to Clojure — uncurry multi-arg functions for flat calls
        clj-form (ansatz->clj @ansatz-env runtime-body [])
        clj-fn (if (<= n 1)
                 (eval clj-form)
                 ;; Multi-arg: support both flat (f x y) and curried ((f x) y) calls
                 (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) (vec pairs))
                       curried-call (reduce (fn [f s] (list f s))
                                            (list clj-form (first param-syms))
                                            (rest param-syms))]
                   (eval
                    `(fn
                       (~[(first param-syms)]
                        ~(if (= n 2)
                           `(fn [~(second param-syms)] ~curried-call)
                           (reduce (fn [body s] `(fn [~s] ~body))
                                   curried-call
                                   (reverse (rest param-syms)))))
                       (~param-syms ~curried-call)))))]
    (when *verbose* (println "✓" fn-name ":" (pr-str clj-form)))
    clj-fn))

(clojure.core/defn prove-theorem
  "Prove a theorem. Returns nil (side-effect: adds to env).
   Optional ctx: ProofContext for isolated proving (no global mutation)."
  ([thm-name params prop-form tactic-forms]
   (prove-theorem thm-name params prop-form tactic-forms nil))
  ([thm-name params prop-form tactic-forms ctx]
   (let [env (if ctx (:env ctx) (env))
         ;; L3: prop-form may be a PRECOMPUTED kernel Expr goal (the full Π-telescoped statement)
         ;; rather than a surface s-expr — this lets generic/generated laws use the high-level
         ;; tactic block instead of hand-building the whole proof TERM. In that mode `params` is a
         ;; vector of binder NAMES to intro (or empty, letting the tactic block control intros).
         expr-goal? (instance? ansatz.kernel.Expr prop-form)
         pairs (when-not expr-goal? (parse-params params))
         ;; P3 of the elaborator unification: the goal telescope (binders may depend on
         ;; earlier binders — hypothesis Props routinely do — and the prop on all of them)
         ;; elaborates fvar-first via elab-signature; binder types and the statement go
         ;; through the SAME elaborator as function bodies (lean4: one elaborator for
         ;; terms and tactic goals).
         goal-type (if expr-goal? prop-form (:type-ansatz (elab-signature env pairs prop-form)))
         [ps _] (proof/start-proof env goal-type)
         intro-names (if expr-goal? (mapv str params) (mapv (comp str first) pairs))
         ps (if (seq intro-names) (basic/intros ps intro-names) ps)
         ps (reduce run-tactic ps tactic-forms)]
     (when-not (proof/solved? ps)
       (throw (ex-info (str "Proof incomplete\n" (proof/format-goals ps)) {:ps ps})))
     (extract/verify ps)
     (let [term (extract/extract ps)
           final-env (:env ps)
           cname (name/from-string (str thm-name))
           ci (env/mk-thm cname [] goal-type term)]
       ;; When using a context, add to context's env.
       ;; When using global, swap! to avoid stale env race.
       (if ctx
         (env/check-constant final-env ci)
         (swap! ansatz-env (fn [_] (env/check-constant final-env ci)))))
     (when *verbose* (println "✓" thm-name "proved")))))

(clojure.core/defn prove-law
  "Like `prove-theorem`, but RETURNS `[goal-type proof-term]` and does NOT install — for callers that
   register the law themselves (e.g. wandler's `thm!` = `(mk-thm name [] goal proof)`). Lets a
   hand-built `[goal proof]` proof migrate to the thin tactic surface without touching the
   registration plumbing. `params`+`prop-form` are surface forms (or `prop-form` a precomputed Expr
   goal with `params` = binder names); `tactic-forms` is the tactic block. Verifies before returning."
  [params prop-form tactic-forms]
  (let [env (env)
        expr-goal? (instance? ansatz.kernel.Expr prop-form)
        pairs (when-not expr-goal? (parse-params params))
        goal-type (if expr-goal? prop-form (:type-ansatz (elab-signature env pairs prop-form)))
        [ps _] (proof/start-proof env goal-type)
        intro-names (if expr-goal? (mapv str params) (mapv (comp str first) pairs))
        ps (if (seq intro-names) (basic/intros ps intro-names) ps)
        ps (reduce run-tactic ps tactic-forms)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "Proof incomplete\n" (proof/format-goals ps)) {:ps ps})))
    (extract/verify ps)
    [goal-type (extract/extract ps)]))

;; ============================================================
;; Law registration — idempotent + NON-SWALLOWING (the registry helper)
;; ============================================================
;; Runtime law libraries (e.g. wandler) install proven theorems into the global
;; env as a side effect of loading. Lean does this at elaboration time and fails
;; LOUDLY; we install at runtime, so callers grew an ad-hoc
;;   (when-not (has? "X") (try (eval '(theorem …)) (catch Throwable _ nil)))
;; around every law. The `catch _ nil` silently swallows proof failures — a broken
;; law just never gets admitted, surfacing only as a missed optimization. This
;; helper is the clean replacement: idempotent via `has-constant?`, and it
;; RE-RAISES by default so a regression is seen, not hidden.

(def ^:dynamic *install-ledger*
  "When bound to an atom, `install-theorem!` conj's an entry
   {:name s, :status :present|:admitted|:failed [, :error msg]} per call, so an
   installer can report admitted-vs-skipped counts. nil = no ledger (default)."
  nil)

(clojure.core/defn has-constant?
  "True if constant `s` (string or symbol) is already in the current env. The
   idempotency predicate behind `install-theorem!` — replaces the open-coded
   `(some? (env/lookup (env) (name/from-string s)))` each law file repeats."
  [s]
  (some? (env/lookup (env) (name/from-string (str s)))))

(clojure.core/defn- record-install!
  [nm status err]
  (when *install-ledger*
    (swap! *install-ledger* conj (cond-> {:name nm :status status}
                                   err (assoc :error (.getMessage ^Throwable err)))))
  (when (and *verbose* (= status :failed))
    (println "✗" nm "failed to install:" (.getMessage ^Throwable err)))
  status)

(clojure.core/defn install-theorem!
  "Idempotent, NON-SWALLOWING law registration — the clean replacement for the
   `(when-not (has? \"X\") (try (eval '(theorem …)) (catch Throwable _ nil)))`
   pattern. If `thm-name` is already present, no-op (returns :present). Otherwise
   prove it via `prove-theorem` (verifies + installs). On proof failure: RE-RAISE
   by default (a broken law must not silently vanish); under `:lenient? true`,
   record the failure to `*install-ledger*` and return :failed instead of throwing.

   `params`/`prop-form`/`tactic-forms` are exactly what `prove-theorem` takes
   (surface forms, or a precomputed Expr goal with `params` = binder names). No
   `eval` needed for literal forms — pass the quoted data directly; reserve `eval`
   only for programmatically-assembled tactic blocks. Returns the status keyword."
  [thm-name params prop-form tactic-forms & {:keys [lenient?]}]
  (let [nm (str thm-name)]
    (if (has-constant? nm)
      (record-install! nm :present nil)
      (if lenient?
        (try (prove-theorem thm-name params prop-form tactic-forms)
             (record-install! nm :admitted nil)
             (catch Throwable e (record-install! nm :failed e)))
        (do (prove-theorem thm-name params prop-form tactic-forms)
            (record-install! nm :admitted nil))))))

(defmacro install-guarded!
  "Idempotent, NON-SWALLOWING guard for PROGRAMMATIC law installs that don't fit `deftheorem` —
   raw-term `env/check-constant` admits, `admit!`s of generated equations, programmatically-assembled
   `theorem`/`defn` forms. `(install-guarded! \"Name\" body...)` runs `body` (which must add the
   constant `Name` to the env) only when `Name` is absent, and RE-RAISES on failure — replacing the
   silent `(when-not (has? \"Name\") (try body (catch Throwable _ nil)))` that hid proof regressions.
   For a genuinely-deferred install, catch + log explicitly at the call site instead of using this."
  [name & body]
  `(when-not (has-constant? ~name)
     ~@body))

;; ============================================================
;; Macros
;; ============================================================

;; ============================================================
;; Public macros — clean names (preferred) and legacy c-prefixed
;; ============================================================

(clojure.core/defn tag-kernel-name
  "Attach the kernel constant name to a compiled fn (no-op for non-IObj values)."
  [f fn-name]
  (if (instance? clojure.lang.IObj f)
    (vary-meta f assoc :ansatz.core/kernel-name (str fn-name))
    f))

(clojure.core/defn- csimp-head
  "The const-name head of one side of a csimp equation: a bare symbol `f`, or the head of an
   application `(f …)`. Used to read the f→g of a proven `f = g`."
  [term]
  (cond
    (symbol? term) (str term)
    (seq? term)    (recur (first term))
    :else          nil))

(clojure.core/defn define-csimp
  "Register a kernel-VERIFIED compiler replacement — ansatz's @[csimp]. Proves `f = g` via
   prove-theorem (which kernel-checks it via env/check-constant, throwing if invalid), then records
   f→g in the :csimp Env extension. Codegen (ansatz.codegen/csimp-target) then emits g wherever f
   appears, GUARDED by lowerability — exactly Lean's @[csimp]: the proof is the licence, the swap
   happens in COMPILED code only. f and g are the const heads of the equation's two sides. Returns [f g]."
  [eq-name params prop-form tactic-forms]
  (prove-theorem eq-name params prop-form tactic-forms)
  (let [f (csimp-head (nth prop-form 2 nil))
        g (csimp-head (nth prop-form 3 nil))]
    (when (and f g)
      (swap! ansatz-env env/update-extension :csimp {} assoc f g)
      (when *verbose* (println "✓ csimp:" f "→" g "(verified replacement)")))
    [f g]))

(defmacro defn
  "Define a verified function. Types are METADATA on the binders and the name — the binding vector
   stays a normal Clojure vector, so typing composes (add types without reshaping the form):
     (a/defn ^Nat double [^Nat n] (+ n n))
     (a/defn ^{:- (List Nat)} squares [^{:- (List Nat)} xs] (map (fn [x] (* x x)) xs))
   ^Type is the simple-type shorthand; ^{:- T} carries compound types. The legacy :- separator form
   is still accepted (auto-detected):
     (a/defn double [n :- Nat] Nat (+ n n))
   Well-founded recursion: put  :termination-by <measure>  before the body."
  [fn-name params & more]
  (let [meta?    (metadata-params? params)
        ;; Gradual-typing surface: a PLAIN parameter vector (bare symbols, no ^Type metadata,
        ;; no :- forms, no return annotation) consults the malli function-schema registry —
        ;; (m/=> foo [:=> [:cat …] …]) or ^{:malli/schema …} on the name — so ordinary
        ;; instrumented Clojure ports by changing `defn` to `a/defn` with schemas unchanged.
        ;; ansatz.malli loads lazily; without malli on the classpath this probe is a no-op
        ;; (requiring-resolve at the optionality seam). A registered-but-untranslatable
        ;; schema THROWS honestly rather than lifting approximately.
        msig     (when (and (vector? params) (seq params) (every? symbol? params)
                            (not meta?) (nil? (binder-type fn-name)))
                   (try (when-let [f (requiring-resolve 'ansatz.malli/signature-for)]
                          (f (ns-name *ns*) fn-name (count params)))
                        (catch java.io.FileNotFoundException _ nil)))
        params   (if msig
                   (vec (mapcat (fn [p t] [p :- t]) params (:param-types msig)))
                   params)
        ret-type (cond meta? (binder-type fn-name)
                       msig  (:ret-type msig)
                       :else (first more))
        body-and-opts (if (or meta? msig) more (rest more))
        [opts body] (if (= :termination-by (first body-and-opts))
                      [{:termination-by (second body-and-opts)} (nth body-and-opts 2)]
                      [{} (first body-and-opts)])
        partial? (:partial (meta fn-name))
        nm (vary-meta fn-name dissoc :- :tag :partial)]
    ;; the compiled fn carries its kernel constant name as metadata — runtimes use it
    ;; to find the definition from the VALUE (e.g. generative checkers)
    (cond
      partial?
      `(def ~nm (tag-kernel-name (define-partial '~nm '~params '~ret-type '~body) '~nm))
      (:termination-by opts)
      `(def ~nm (tag-kernel-name (define-verified-wf '~nm '~params '~ret-type '~body '~(:termination-by opts)) '~nm))
      :else
      `(def ~nm (tag-kernel-name (define-verified '~nm '~params '~ret-type '~body) '~nm)))))

(defmacro foreign
  "Declare a TRUSTED FOREIGN function — an arbitrary Clojure fn asserted at a kernel type,
   the gradual escape hatch / typed FFI hole. The body is NOT elaborated or verified: the
   type is admitted as an axiom (trusted) and `impl` is the runtime. Usable in verified
   bodies — the optimizer fuses/rewrites PARAMETRICALLY around it (the laws hold for any
   function), and codegen calls `impl`. The asserted type is the entire trust boundary.
     (a/foreign sqrt [x :- Float] Float (fn [x] (Math/sqrt x)))
     (a/foreign upper [s :- String] String clojure.string/upper-case)
   Then `(map (fn [x] (sqrt x)) xs)` in an a/defn body verifies + optimizes the pipeline
   structure while `sqrt` stays a trusted hole."
  [fn-name params ret-type impl]
  (let [nm (vary-meta fn-name dissoc :- :tag)]
    `(def ~nm (do (define-foreign '~nm '~params '~ret-type)
                  (tag-kernel-name ~impl '~nm)))))

(defmacro implemented_by
  "Lean's @[implemented_by] / @[extern] correspondence, named to match — an alias of `a/foreign`:
   assert a Clojure `impl` at a kernel type as a trusted hole. The type is the entire trust boundary;
   `impl` is the runtime. Verified bodies reason parametrically around it; codegen calls `impl`.
     (a/implemented_by sqrt [x :- Float] Float (fn [x] (Math/sqrt x)))"
  [fn-name params ret-type impl]
  `(foreign ~fn-name ~params ~ret-type ~impl))

(defmacro csimp
  "Register a kernel-VERIFIED compiler replacement — ansatz's @[csimp]. Prove `f = g`; codegen then
   emits g wherever f appears (g the faster/runnable form, justified by the proof). Like Lean's
   @[csimp]: the proof is the licence, and the swap is in COMPILED code only (never in proofs).
     (a/csimp len-eq [] (= (-> (List Nat) Nat) List.length List.lengthTR) (rfl))
   The replacement only fires when g is lowerable, so inherited compiler-internal targets are skipped."
  [eq-name params prop & tactics]
  `(define-csimp '~eq-name '~params '~prop '~(vec tactics)))

(defmacro theorem
  "Prove a theorem.
   (a/theorem add-zero [n :- Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))"
  [thm-name params prop & tactics]
  `(prove-theorem '~thm-name '~params '~prop '~(vec tactics)))

(defmacro deftheorem
  "Idempotent, NON-SWALLOWING `theorem`: proves + installs `thm-name` unless it is
   already present; RE-RAISES on failure. Sugar over `install-theorem!` for literal
   forms — the drop-in for `(theorem …)` in runtime install paths (no eval/try/catch
   needed). For the ledger / lenient mode, call `install-theorem!` directly.
   (a/deftheorem add-zero [n :- Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))"
  [thm-name params prop & tactics]
  `(install-theorem! '~thm-name '~params '~prop '~(vec tactics)))

(defmacro inductive
  "Define an inductive type with constructors.
   (a/inductive Color [] (red) (green) (blue))
   (a/inductive Color [] (red) (green) (blue) :deriving [DecidableEq])

   Indexed families use :indices and :where clauses:
   (a/inductive Vec [α Type] :indices [n Nat]
     (nil :where [0])
     (cons [a α] [m Nat] [tail (Vec α m)] :where [(+ m 1)]))"
  [type-name params & body]
  (let [;; Split :in option from body
        [opts body] (if (= :in (first body))
                      [{:in (second body)} (drop 2 body)]
                      [{} body])
        ;; Split :indices option from body
        [opts body] (if (= :indices (first body))
                      [(assoc opts :indices (second body)) (drop 2 body)]
                      [opts body])
        ;; Split :deriving option from end of body
        body-vec (vec body)
        [opts body-vec] (let [n (count body-vec)]
                          (if (and (>= n 2)
                                   (= :deriving (nth body-vec (- n 2))))
                            [(assoc opts :deriving (nth body-vec (- n 1)))
                             (subvec body-vec 0 (- n 2))]
                            [opts body-vec]))
        ctors body-vec
        ;; Parse a single constructor form, splitting off :where clause
        parse-ctor (fn [c]
                     (if (sequential? c)
                       (let [cname (first c)
                             parts (rest c)
                             ;; Split fields and :where clause
                             where-idx (.indexOf (vec parts) :where)
                             [fields where-exprs]
                             (if (neg? where-idx)
                               [parts nil]
                               [(take where-idx parts)
                                (first (drop (inc where-idx) parts))])
                             flat-fields (vec (apply concat fields))]
                         (if where-exprs
                           [cname flat-fields (vec where-exprs)]
                           [cname flat-fields]))
                       [c []]))
        ctor-specs (mapv parse-ctor ctors)
        deriving-classes (:deriving opts)]
    `(do (inductive/define-inductive (env) ~(str type-name) '~params '~ctor-specs
           ~@(when (:in opts) [:in `'~(:in opts)])
           ~@(when (:indices opts) [:indices `'~(:indices opts)]))
         ~@(when deriving-classes
             [`(let [env# @ansatz-env
                     env'# ((requiring-resolve 'ansatz.deriving/run-deriving!)
                            env# ~(str type-name) '~ctor-specs '~deriving-classes)]
                 (reset! ansatz-env env'#))])
         ;; lean4 auto-derives SizeOf for every inductive — best-effort, no-op when unsupported
         (wf-derive-sizeof! ~(str type-name))
         nil)))

;; ============================================================
;; structure — single-constructor inductive with projections
;; ============================================================
;; Following Lean 4: structures are single-constructor inductives with
;; auto-generated projection functions. At the kernel level, projections
;; use Expr.proj (the kernel projection primitive).
;;
;; (a/structure Pair [α Type β Type] (fst α) (snd β))
;; Generates:
;;   - Pair inductive type with mk constructor
;;   - Pair.fst : ∀ {α β}, Pair α β → α  (projection using Expr.proj)
;;   - Pair.snd : ∀ {α β}, Pair α β → β

(clojure.core/defn add-inherited-accessors!
  "For a structure CHILD that `:extends` PARENT (embedded as the packed subobject field
   `to{PARENT}`), generate the inherited field accessors — following Lean 4's subobject model
   (../lean4 Structure.lean: `fromSubobject` fields have no own projection; access is the parent
   projection composed with the subobject projection). Lean inlines this at elaboration; we have
   no subobject-aware dot-notation, so we materialize each as an `:abbrev` def
     CHILD.f := λ {params} (s : CHILD params) => PARENT.f params (CHILD.to{PARENT} params s)
   which unfolds to exactly that composition. Parent field names come from the structure-registry
   (the parent was defined via `a/structure`). Skips any field the child overrides (its own
   projection wins) and the already-generated `to{PARENT}` projection. `n-params` = carrier arity."
  [child-str parent-str to-field n-params]
  (let [env0 (env)
        child-name (name/from-string child-str)
        parent-fields (get-in @@(requiring-resolve 'ansatz.core/structure-registry)
                              [parent-str :fields])
        ci (env/lookup env0 child-name)
        lvl-params (vec (.levelParams ^ConstantInfo ci))
        lvl-levels (mapv lvl/param lvl-params)
        ind-type (.type ^ConstantInfo ci)
        param-types (loop [t ind-type i 0 acc []]
                      (if (and (< i n-params) (e/forall? t))
                        (recur (e/forall-body t) (inc i) (conj acc (e/forall-type t)))
                        acc))
        ;; Self's type: CHILD p…, at depth n-params (self not yet bound) → param i = bvar(n-params-i-1)
        ind-applied (reduce (fn [a i] (e/app a (e/bvar (- n-params i 1))))
                            (e/const' child-name lvl-levels) (range n-params))
        ;; Inside (λ {params} (self) => BODY): self = bvar 0, param i = bvar(n-params - i)
        param-bvar (fn [i] (e/bvar (- n-params i)))
        ;; CHILD.to{PARENT} params self  : PARENT p…
        to-app (e/app (reduce (fn [a i] (e/app a (param-bvar i)))
                              (e/const' (name/from-string (str child-str "." to-field)) lvl-levels)
                              (range n-params))
                      (e/bvar 0))]
    (doseq [f parent-fields
            :let [child-f (name/from-string (str child-str "." f))]
            :when (not (env/lookup (env) child-f))]
      (let [parent-f (reduce (fn [a i] (e/app a (param-bvar i)))
                             (e/const' (name/from-string (str parent-str "." f)) lvl-levels)
                             (range n-params))
            body (e/app parent-f to-app)
            val  (e/lam "self" ind-applied body :default)
            val  (loop [i (dec n-params) b val]
                   (if (< i 0) b (recur (dec i) (e/lam "p" (nth param-types i) b :implicit))))
            ty   (tc/infer-type (tc/mk-tc-state (env)) val)
            cidef (env/mk-def child-f lvl-params ty val :hints :abbrev)]
        (reset! @(requiring-resolve 'ansatz.core/ansatz-env)
                (env/check-constant (env) cidef))))))

(clojure.core/defn rewrite-inherited-field-refs
  "Rewrite bare references to a parent's field names inside a child structure field-type form
   into explicit subobject projections — mirroring Lean's `fromSubobject` resolution (../lean4
   Structure.lean: parent fields are opened into scope as projections of the subobject while
   elaborating child fields). A reference to parent field `f` becomes `(Parent.f carrier… toField)`:
   the parent projection applied (carrier args explicit) to the embedded subobject. This keeps the
   child's axiom fields (e.g. `mul_add : mul a (add b c) = …`) admissible by the existing field
   compiler with no changes to it. `field-set` = parent field-name strings; `carrier-args` = the
   carrier s-exprs from `:extends (Parent carrier…)`; `to-field` = the subobject field symbol.
   Assumes no local binder shadows a parent field name (parent fields are ops/axioms like add/zero;
   child binders are a/b/c — no collision)."
  [form field-set parent-sym carrier-args to-field]
  (cond
    (and (symbol? form) (contains? field-set (str form)))
    (apply list (symbol (str parent-sym "." form)) (concat carrier-args [to-field]))
    (seq? form)
    (apply list (map #(rewrite-inherited-field-refs % field-set parent-sym carrier-args to-field) form))
    (vector? form)
    (mapv #(rewrite-inherited-field-refs % field-set parent-sym carrier-args to-field) form)
    :else form))

(defmacro structure
  "Define a structure (single-constructor inductive with projections).

   (a/structure Pair [α Type β Type] (fst α) (snd β))

   Fields are specified as (name type) pairs. The constructor is always 'mk'.
   Projection functions are automatically generated.

   Inheritance (Lean-4 subobject model):
     (a/structure WSemiring [S Type] :extends (WAddMonoid S)
       (mul (=> S S S)) (mul_add ...) ...)
   The parent is embedded as a packed `to{Parent}` field (field 0); `Child.to{Parent}` is its
   projection and inherited accessors `Child.<parentField>` are generated (see EXTENDS_DESIGN.md).
   Single inheritance only for now — multiple `:extends` parents are rejected."
  [type-name params & fields]
  (let [;; Consume leading option pairs (:in, :extends) in any order
        [opts fields] (loop [o {} fs fields]
                        (if (and (keyword? (first fs)) (#{:in :extends} (first fs)))
                          (recur (assoc o (first fs) (second fs)) (drop 2 fs))
                          [o fs]))
        extends-form (:extends opts)
        _ (when (and extends-form (not (and (sequential? extends-form) (symbol? (first extends-form)))))
            (throw (ex-info "structure :extends expects a single (Parent carrier…) form; multiple inheritance not yet implemented"
                            {:extends extends-form})))
        parent-sym (when extends-form (first extends-form))
        to-field   (when parent-sym (symbol (str "to" parent-sym)))
        ;; Parse fields: (name type) pairs
        base-field-specs (mapv (fn [f]
                                 (if (sequential? f)
                                   [(first f) (second f)]
                                   (throw (ex-info "structure field must be (name type)" {:field f}))))
                               fields)
        ;; Prepend the packed subobject field (Lean's `subobject` kind) when extending
        field-specs (if extends-form
                      (into [[to-field extends-form]] base-field-specs)
                      base-field-specs)
        ;; Build the flat field vector for the constructor: [name1 type1 name2 type2 ...]
        flat-fields (vec (mapcat identity field-specs))
        ;; Single constructor named 'mk'
        ctor-spec ['mk flat-fields]]
    `(do
       ;; Define the inductive with single constructor. When extending, rewrite inherited-field
       ;; references in the new fields' types to subobject projections at runtime (parent field
       ;; names come from the registry, available once the parent is defined).
       ~(if extends-form
          `(let [pfields# (set (get-in @@(requiring-resolve 'ansatz.core/structure-registry)
                                       [~(str parent-sym) :fields]))
                 new-specs# (mapv (fn [[fn# ft#]]
                                    [fn# (rewrite-inherited-field-refs
                                          ft# pfields# '~parent-sym '~(vec (rest extends-form)) '~to-field)])
                                  '~base-field-specs)
                 flat# (vec (mapcat identity (into [['~to-field '~extends-form]] new-specs#)))]
             (inductive/define-inductive (env) ~(str type-name) '~params [[(symbol "mk") flat#]]
               ~@(when (:in opts) [:in `'~(:in opts)])))
          `(inductive/define-inductive (env) ~(str type-name) '~params '~[ctor-spec]
             ~@(when (:in opts) [:in `'~(:in opts)])))

       ;; Generate projection functions
       ;; Each projection is: λ {params...} (x : T params) => proj T.name idx x
       ;; Following Lean 4: use Expr.proj (kernel primitive) with TC-inferred types.
       ~@(map-indexed
          (fn [idx [fname _ftype]]
            (let [proj-name (str type-name "." fname)
                  n-params (/ (count params) 2)]
              `(let [env# (env)
                     type-name# (name/from-string ~(str type-name))
                     proj-name# (name/from-string ~proj-name)
                     _# (when-not (env/lookup env# proj-name#)
                          (let [ci# (env/lookup env# type-name#)
                                ind-type# (.type ci#)
                                lvl-params# (vec (.levelParams ci#))
                                lvl-levels# (mapv lvl/param lvl-params#)
                                n-params# ~n-params
                                 ;; Extract param types from the inductive type forall telescope
                                param-types# (loop [t# ind-type# i# 0 types# []]
                                               (if (and (< i# n-params#) (e/forall? t#))
                                                 (recur (e/forall-body t#) (inc i#) (conj types# (e/forall-type t#)))
                                                 types#))
                                 ;; Build the applied inductive type at depth n-params
                                ind-applied# (reduce (fn [acc# i#]
                                                       (e/app acc# (e/bvar (- n-params# i# 1))))
                                                     (e/const' type-name# lvl-levels#)
                                                     (range n-params#))
                                 ;; Build value: λ {params...} (x : T params) => proj T idx x
                                proj-val# (e/proj type-name# ~idx (e/bvar 0))
                                proj-val# (e/lam "self" ind-applied# proj-val# :default)
                                proj-val# (loop [i# (dec n-params#) body# proj-val#]
                                            (if (< i# 0) body#
                                                (recur (dec i#)
                                                       (e/lam "p" (nth param-types# i#) body# :implicit))))
                                 ;; Infer type from value using TC (avoids manual bvar computation)
                                st# (tc/mk-tc-state env#)
                                proj-type# (tc/infer-type st# proj-val#)
                                 ;; Add as abbrev definition
                                proj-ci# (env/mk-def proj-name# lvl-params# proj-type# proj-val#
                                                     :hints :abbrev)]
                            (reset! @(requiring-resolve 'ansatz.core/ansatz-env)
                                    (env/check-constant env# proj-ci#))))])))
          field-specs)

       ;; Inherited accessors for the embedded parent (Lean subobject `fromSubobject` access).
       ;; Runs after the projection loop so Child.to{Parent} exists.
       ~@(when extends-form
           [`(add-inherited-accessors! ~(str type-name) ~(str parent-sym)
                                       ~(str to-field) ~(/ (count params) 2))])

       ;; Emit Clojure defrecord for runtime representation
       ;; The record has keyword-accessible fields: (:x point), (:y point)
       ;; Idempotent across namespaces/re-installs: a record class cannot be re-imported into a
       ;; namespace, so a second definition of the same structure (e.g. an env reset then re-install)
       ;; would throw "already refers to". Skip the defrecord if the class is already defined.
       (when-not (instance? Class (resolve '~type-name))
         (defrecord ~type-name ~(mapv (fn [[fname _]] (symbol (str fname))) field-specs)))

       ;; Register in structure-registry for ansatz->clj compilation
       (swap! @(requiring-resolve 'ansatz.core/structure-registry)
              assoc ~(str type-name)
              {:fields ~(mapv (fn [[fname _]] (str fname)) field-specs)
               :ctor-sym '~(symbol (str "->" type-name))})

       nil)))

;; ============================================================
;; do-notation — monadic syntax sugar
;; ============================================================
;; Pure desugaring to Bind.bind and Pure.pure applications.
;; Following Lean 4: no kernel support needed.

(clojure.core/defn do*
  "Desugar do-notation into Bind.bind / Pure.pure s-expressions.
   Used inside a/defn bodies (s-expression level, not macro).

   Syntax:
     (a/do* [x <- expr1]
            [_ <- expr2]
            (Pure.pure result))

   Desugars to:
     (Bind.bind expr1 (fn [x] (Bind.bind expr2 (fn [_] (Pure.pure result)))))

   The Bind.bind and Pure.pure constants come from the store (Init/Mathlib).
   Works with any monad that has Bind and Pure instances."
  [& steps]
  (if (= 1 (count steps))
    ;; Last step: return as-is (should be a pure/return expression)
    (first steps)
    (let [step (first steps)
          rest-steps (rest steps)]
      (if (and (vector? step) (= '<- (second step)))
        ;; Bind step: [x <- expr] => (Bind.bind expr (fn [x] rest))
        (let [var-name (first step)
              expr (nth step 2)]
          (list 'Bind.bind expr (list 'fn [var-name] (apply do* rest-steps))))
        ;; Statement step (no binding): expr => (Bind.bind expr (fn [_] rest))
        (list 'Bind.bind step (list 'fn ['_] (apply do* rest-steps)))))))
