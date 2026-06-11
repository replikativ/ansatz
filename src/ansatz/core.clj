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
            [ansatz.export.storage :as storage]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.tactic.instance :as instance]
            [ansatz.inductive :as inductive]
            [ansatz.surface.match :as surface-match]
            [ansatz.surface.ingest :as ingest]
            [ansatz.surface.elaborate :as elab]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; State
;; ============================================================

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

;; Global atoms — REPL convenience wrappers around ProofContext
(defonce ansatz-env (atom nil))
(defonce ansatz-instance-index (atom nil))

;; Extensible registries — declared early so sexp->ansatz can reference them.
;; Lean 4 equivalents: @[tactic], @[simproc], elab_rules
(defonce ^{:doc "Open tactic registry. Maps symbol → (fn [ps args] → ps')."} tactic-registry (atom {}))
(defonce ^{:doc "Custom elaborator registry. Maps symbol → (fn [env scope depth args lctx] → Expr)."} elaborator-registry (atom {}))
(defonce ^{:doc "Persistent simproc registry. Vector of (fn [st expr] → result|nil)."} simproc-registry (atom []))
;; Arity registry for Clojure compilation — following Lean 4's LCNF arity analysis.
;; Maps Name-string → {:arity n :erased k} where n = explicit params, k = erased prefix.
;; Used by ansatz->clj to emit flat multi-arg calls (FAP) instead of curried calls.
(defonce ^{:doc "Arity registry for compiled functions."} arity-registry (atom {}))
;; Structure registry — maps type-name → {:fields [field-name ...], :record-sym symbol}
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
(defonce ^{:doc "Optimizer hook for the runtime. nil or (fn [env term] → term')."} optimize-hook (atom nil))
;; SEAM — codegen: head-constant Name-string → (fn [env expr names] → clj-form). ansatz->clj consults
;; it for application heads it does not lower natively (e.g. List.map → wandler's amapl). Base kernel
;; codegen stays in ansatz; the runtime adds collection/relational lowering additively.
(defonce ^{:doc "Codegen registry: Name-string → (fn [env expr names] → clj-form)."} codegen-registry (atom {}))

;; ── Incremental Clojure ingestion ───────────────────────────────────────────────────────────────
;; The elaborator macroexpand-1's ANY clojure.core (or user) macro on the way in — so all the
;; binding/threading/sugar reaches the kernel as core forms (let*/fn*/if/application) without a case
;; per macro — EXCEPT a small exclusion set: forms ansatz handles with a dedicated typed elaborator
;; that beats the macro's expansion. `->` is the type arrow (not threading); `cond` has a typed
;; handler (cond->if) that maps :else correctly, unlike Clojure's :else-as-truthy expansion.
;; Soundness does NOT depend on this set: the kernel type-checks every resulting term, so a macro
;; that expands to a non-CIC form simply fails to elaborate (an honest error) — it can never produce
;; an unsound definition. The set only keeps OUR handlers winning and errors clean.
;; Re-exported from ansatz.surface.ingest (shared, breaks the core↔elaborate cycle).
(def no-expand-macros ingest/no-expand-macros)
(def expand-macro? ingest/expand-macro?)

(clojure.core/defn init!
  "Load Ansatz environment from LMDB store and build instance index."
  [store-path branch]
  (let [sm (storage/open-store store-path)
        env (storage/load-env sm branch)]
    (reset! ansatz-env env)
    ;; Build instance index:
    ;; 1. Try loading from TSV (Lean 4 export, complete)
    ;; 2. Fall back to name-based discovery (~200ms, partial)
    (let [;; Try to find instances.tsv relative to working dir or in resources/
          tsv-candidates ["resources/instances.tsv" "instances.tsv"
                          (str store-path "/instances.tsv")]
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
                 (count idx) "classes indexed")))))

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
      (when *verbose* (println "Ansatz: Init loaded —" (.size ^ansatz.kernel.Env @ansatz-env) "declarations"))
      @ansatz-env)))

(clojure.core/defn env [] (or @ansatz-env (throw (ex-info "Call (ansatz/init!) or (ansatz/load-init!) first" {}))))
(clojure.core/defn instance-index [] (or @ansatz-instance-index {}))

(declare synth-cache)

;; Dynamic vars for elaboration context threading
(def ^:dynamic *scope-types* {})
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
   (let [cache (or cache-atom synth-cache)]
     (if-let [cached (find @cache goal-type)]
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
         (swap! cache assoc goal-type (or result ::miss))
         result)))))

(clojure.core/defn- get-arg-type
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
;; Sexp → Ansatz Expr compiler (the ONE compiler for everything)
;; ============================================================

(declare sexp->ansatz parse-params)

;; Type context for outer-scope variables — used by match handler to
;; register fvars in the tc's local context. Maps symbol → Expr (type).
;; Set by build-telescope when compiling function bodies.
;; *scope-types* and *current-lctx* are defined at the top of the file.

(clojure.core/defn- build-telescope
  "Build nested foralls or lambdas from param pairs.
   ctor: e/forall' or e/lam.
   Each pair is [name type-form] or [name type-form binder-info]."
  [env scope depth pairs body-form ctor]
  (if (empty? pairs)
    (sexp->ansatz env scope depth body-form)
    (let [pair (first pairs)
          pname (first pair)
          ptype-form (second pair)
          binfo (if (>= (count pair) 3) (nth pair 2) :default)
          ptype (sexp->ansatz env scope depth ptype-form)
          new-scope (assoc scope pname depth)
          body (binding [*scope-types* (assoc *scope-types* pname ptype)]
                 (build-telescope env new-scope (inc depth) (rest pairs) body-form ctor))]
      (ctor (str pname) ptype body binfo))))

(clojure.core/defn- cond->if
  "Desugar a flat cond clause list `(c1 e1 c2 e2 … :else en)` to nested `if`."
  [clauses]
  (if (empty? clauses)
    (throw (ex-info "cond: no clause matched and no :else branch" {}))
    (let [[c e & more] clauses]
      (if (= c :else) e (list 'if c e (cond->if more))))))

(clojure.core/defn- scope-bvar-types
  "Map {bvar-index → type} for the binders currently in `scope` (types from *scope-types*), so a
   subterm's enclosing-binder bvars can be typed during elaboration. bvar-index = depth-1-d."
  [scope depth]
  (into {} (keep (fn [[sym d]] (when-let [ty (get *scope-types* sym)] [(- depth 1 d) ty])) scope)))

(clojure.core/defn- infer-value-type
  "Infer the type of an elaborated expression `v-expr` that may mention the enclosing binders as
   bvars 0..depth-1 (types in `bvar-types`, a {bvar-index → type} map). The kernel can't infer a
   term with loose bvars, so we OPEN them to fresh fvars, infer with those fvars registered as
   locals, then ABSTRACT the fvars back — so the resulting type is valid in the original (bvar)
   context. Returns the type Expr, or nil if inference fails."
  [env depth bvar-types v-expr]
  (if (zero? depth)
    (try (tc/infer-type (tc/mk-tc-state env) v-expr) (catch Exception _ nil))
    (let [base (inc (reduce max 6999999 (keys (or *current-lctx* {}))))
          fids (mapv #(+ base %) (range depth))            ; fids[k] replaces bvar k
          v-open (e/instantiate v-expr (mapv e/fvar fids))
          lctx-map (merge (or *current-lctx* {})
                          (into {} (keep (fn [k] (when-let [ty (get bvar-types k)]
                                                   [(nth fids k) {:name (str "_p" k) :type ty
                                                                  :tag :local}]))
                                         (range depth))))
          vt-open (try (tc/infer-type (tc/mk-tc-state-with-locals env lctx-map) v-open)
                       (catch Exception _ nil))]
      (when vt-open
        (e/abstract-many vt-open (vec (reverse fids)))))))   ; close: fids[k] → bvar k

(clojure.core/defn- compile-let*
  "Elaborate `(let* [x1 v1 x2 v2 …] body)` to nested kernel `let` (Lean letE), de-Bruijn style to
   match the rest of the elaborator: each value's type is INFERRED (open-infer-close over the
   enclosing binders), the bound var enters `scope` at the current depth, and the body elaborates
   one binder deeper. This is what makes `let` (and, with accessor elaboration, destructuring) reach
   the kernel."
  [env scope depth bindings body-form lctx]
  (if (empty? bindings)
    (sexp->ansatz env scope depth body-form lctx)
    (let [[x v-form & more] bindings
          v-expr (sexp->ansatz env scope depth v-form lctx)
          vtype (or (infer-value-type env depth (scope-bvar-types scope depth) v-expr)
                    (throw (ex-info (str "let: cannot infer the type of binding " x)
                                    {:binding x :value v-form})))
          scope' (assoc scope x depth)
          body-expr (binding [*scope-types* (assoc *scope-types* x vtype)]
                      (compile-let* env scope' (inc depth) (vec more) body-form lctx))]
      (e/let' (str x) vtype v-expr body-expr))))

(clojure.core/defn sexp->ansatz
  "Compile Clojure s-expression to Ansatz Expr.
   Handles types, terms, operators, binders — everything in one function.
   Optional lctx: local context map {fvar-id → {:name str :type Expr ...}}
   for resolving hypothesis names as fvars."
  ([env scope depth form] (sexp->ansatz env scope depth form nil))
  ([env scope depth form lctx]
   ;; Rebind sexp->ansatz to thread lctx through all recursive calls
   (let [sexp->ansatz (if lctx
                        (fn
                          ([env scope depth form] (sexp->ansatz env scope depth form lctx))
                          ([env scope depth form lctx'] (sexp->ansatz env scope depth form lctx')))
                        sexp->ansatz)]
     (cond
    ;; Handle Clojure nil → Ansatz empty list
       ;; Try to infer element type from return type context, default to Nat
       (nil? form) (let [list-elem-type
                         (or (when *scope-types*
                               (some (fn [[_ ty]]
                                       (let [[h a] (e/get-app-fn-args ty)]
                                         (when (and (e/const? h)
                                                    (= "List" (name/->string (e/const-name h)))
                                                    (seq a))
                                           (first a))))
                                     *scope-types*))
                             (e/const' (name/from-string "Nat") []))]
                     (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                            list-elem-type))
       (integer? form) (e/lit-nat form)
       (string? form) (e/lit-str form)
       (true? form) (e/const' (name/from-string "Bool.true") [])
       (false? form) (e/const' (name/from-string "Bool.false") [])

       (symbol? form)
       (let [s (str form)]
         (cond
        ;; 1. Bound variables (from forall/lambda binders)
           (contains? scope form) (e/bvar (- depth (get scope form) 1))
        ;; 2. Local context (hypothesis fvars) — checked before global env
           (and lctx (some (fn [[id d]] (when (= s (:name d)) id)) lctx))
           (e/fvar (some (fn [[id d]] (when (= s (:name d)) id)) lctx))
        ;; 3. Built-in types and global constants
           (= s "Prop")  (e/sort' lvl/zero)
           (= s "Type")  (e/sort' (lvl/succ lvl/zero))
           (= s "Nat")   (e/const' (name/from-string "Nat") [])
           (= s "Int")   (e/const' (name/from-string "Int") [])
           (= s "Real")  (e/const' (name/from-string "Real") [])
           (= s "Bool")  (e/const' (name/from-string "Bool") [])
           (= s "True")  (e/const' (name/from-string "True") [])
           (= s "False") (e/const' (name/from-string "False") [])
        ;; Collection types (need level 0 for Nat elements)
           (= s "List")  (e/const' (name/from-string "List") [lvl/zero])
        ;; Constructors with Clojure-safe names
           (= s "nil")   (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                                (or (when *scope-types*
                                      (some (fn [[_ ty]]
                                              (let [[h a] (e/get-app-fn-args ty)]
                                                (when (and (e/const? h)
                                                           (= "List" (name/->string (e/const-name h)))
                                                           (seq a))
                                                  (first a))))
                                            *scope-types*))
                                    (e/const' (name/from-string "Nat") [])))
           (= s "cons")  (e/const' (name/from-string "List.cons") [lvl/zero])
           :else
           (if-let [ci (env/lookup env (name/from-string s))]
             (let [lps (vec (.levelParams ^ConstantInfo ci))]
               (e/const' (name/from-string s)
                         (if (empty? lps) []
                        ;; Default level: zero for most things, succ zero for Eq/Iff
                        ;; Heuristic: if the constant's result type is Sort 0 (Prop),
                        ;; use succ zero. Otherwise use zero.
                             (let [default-lvl (if (or (.endsWith s "Eq") (.endsWith s "Iff")
                                                       (.endsWith s "HEq"))
                                                 (lvl/succ lvl/zero)
                                                 lvl/zero)]
                               (mapv (fn [_] default-lvl) lps)))))
             (throw (ex-info (str "Unknown: " s) {:scope (keys scope)})))))

       ;; Incremental macroexpansion: expand any macro (except no-expand-macros) and re-elaborate,
       ;; so Clojure's binding/threading/sugar reaches the kernel as core forms. Registered
       ;; elaborators and ansatz's own typed handlers still win (checked here / below).
       (and (sequential? form) (seq form)
            (expand-macro? (first form))
            (nil? (get @elaborator-registry (first form))))
       (sexp->ansatz env scope depth (macroexpand-1 form) lctx)

       (and (sequential? form) (seq form))
    ;; Check custom elaborator registry first
       (if-let [elab-fn (get @elaborator-registry (first form))]
         (elab-fn env scope depth (vec (rest form)) lctx)
         ;; Keyword projection: (:field-name struct) → structure projection
         (if (keyword? (first form))
           (let [field-name (name (first form))
                 struct-expr (sexp->ansatz env scope depth (second form) lctx)
                 struct-type (get-arg-type env
                                           (when (seq scope)
                                             (into {} (keep (fn [[sym d]]
                                                              (when-let [ty (get *scope-types* sym)]
                                                                [(- depth 1 d) ty]))
                                                            scope)))
                                           struct-expr)
                 [th _] (when struct-type (e/get-app-fn-args struct-type))
                 type-name-str (when (and th (e/const? th)) (name/->string (e/const-name th)))
                 struct-info (when type-name-str (get @structure-registry type-name-str))
                 field-idx (when struct-info
                             (first (keep-indexed (fn [i f] (when (= f field-name) i))
                                                  (:fields struct-info))))]
             (if field-idx
               (e/proj (name/from-string type-name-str) field-idx struct-expr)
               (throw (ex-info (str "Unknown structure field: :" field-name)
                               {:field field-name :type type-name-str}))))
           (let [h (str (first form))]
             (case h
        ;; Comparison operators — Prop-valued (LE.le / LT.lt) when 3 args,
        ;; Bool-valued (Nat.ble / Nat.blt) when 2 args.
        ;; (≤ Real a b) or (<= Real a b) → LE.le Real inst a b  (Prop)
        ;; (<= a b) → Nat.ble a b  (Bool, Nat default)
        ;; (≥ Real a b) or (>= Real a b) → LE.le Real inst b a  (Prop)
               ("<" "==" "<=" ">" ">=" "≤" "≥" "≤ᵣ" "≥ᵣ")
               (if (= 4 (count form))
          ;; 3-arg form: (op Type a b) → Prop-valued LE.le / LT.lt
                 (let [type-form (nth form 1)
                       [a-form b-form] (case h
                                         (">" ">=" "≥" "≥ᵣ") [(nth form 3) (nth form 2)]
                                         [(nth form 2) (nth form 3)])
                       rel (case h
                             ("<" ">") "lt"
                             "le")]
                   (sexp->ansatz env scope depth (list (symbol rel) type-form a-form b-form)))
          ;; 2-arg form: (op a b) → Bool-valued Nat comparison
                 (let [[op a-form b-form]
                       (case h
                         ("<"  "≤ᵣ") ["Nat.blt" (nth form 1) (nth form 2)]
                         "==" ["Nat.beq" (nth form 1) (nth form 2)]
                         ("<=" "≤") ["Nat.ble" (nth form 1) (nth form 2)]
                         (">"  "≥ᵣ") ["Nat.blt" (nth form 2) (nth form 1)]
                         (">=" "≥") ["Nat.ble" (nth form 2) (nth form 1)])
                       a (sexp->ansatz env scope depth a-form)
                       b (sexp->ansatz env scope depth b-form)]
                   (e/app* (e/const' (name/from-string op) []) a b)))

        ;; Arithmetic — auto-resolves instances for any type
        ;; (+ a b)        → Nat (default)
        ;; (add Real a b)  → explicit type for Real/Int/etc.
               ("+" "-" "*" "/" "pow" "add" "sub" "mul" "div")
               (let [;; Check if type-annotated: (add Real a b) / (pow Real a b) vs (+ a b)
                     explicit-type? (#{"add" "sub" "mul" "div" "pow"} h)
                     base-op (if explicit-type?
                               (case h "add" "+" "sub" "-" "mul" "*" "div" "/" "pow" "pow")
                               h)
                     [type-name-str type-expr a-form b-form]
                     (if explicit-type?
                       (let [tname (str (nth form 1))]
                         [tname (sexp->ansatz env scope depth (nth form 1))
                          (nth form 2) (nth form 3)])
                       ["Nat" (e/const' (name/from-string "Nat") [])
                        (nth form 1) (nth form 2)])
              ;; Compile operands — coerce Nat literals to target type if needed
                     coerce-lit (fn [e]
                                  (if (and (not= type-name-str "Nat") (e/lit-nat? e))
                             ;; OfNat.ofNat type n inst — for non-Nat types
                                    (let [n (e/lit-nat-val e)
                                   ;; Build OfNat instance: Zero.toOfNat0/One.toOfNat1/natCast
                                          ofnat-inst
                                          (cond
                                            (= n 0) ;; Zero.toOfNat0 type (Zero-inst)
                                            (when-let [zero-inst (resolve-basic-instance env "Zero" type-name-str type-expr)]
                                              (e/app* (e/const' (name/from-string "Zero.toOfNat0") [lvl/zero])
                                                      type-expr zero-inst))
                                            (= n 1) ;; One.toOfNat1 type (One-inst)
                                            (when-let [one-inst (resolve-basic-instance env "One" type-name-str type-expr)]
                                              (e/app* (e/const' (name/from-string "One.toOfNat1") [lvl/zero])
                                                      type-expr one-inst))
                                            :else nil)]
                                      (if ofnat-inst
                                        (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero])
                                                type-expr (e/lit-nat n) ofnat-inst)
                                        e))
                                    e))
                     a (coerce-lit (sexp->ansatz env scope depth a-form))
                     b (if (= base-op "pow")
                  ;; pow exponent is always Nat, don't coerce
                         (sexp->ansatz env scope depth b-form)
                         (coerce-lit (sexp->ansatz env scope depth b-form)))
                     [hop-name basic-class]
                     (case base-op
                       "+"   ["HAdd" "Add"]
                       "-"   ["HSub" "Sub"]
                       "*"   ["HMul" "Mul"]
                       "/"   ["HDiv" "Div"]
                       "pow" ["HPow" "Pow"])]
                 (if (= base-op "pow")
            ;; HPow.hPow α Nat α (instHPow α Nat (Pow-inst)) base exp
            ;; Pow instance chain:
            ;;   Nat: instPowNat Nat instNatPowNat
            ;;   Other (Real, etc.): Monoid.toNatPow α monoid-inst
                   (let [nat (e/const' (name/from-string "Nat") [])
                         pow-inst
                         (if (= type-name-str "Nat")
                           (e/app* (e/const' (name/from-string "instPowNat") [lvl/zero])
                                   nat (e/const' (name/from-string "instNatPowNat") []))
                    ;; General: Monoid.toNatPow α monoid-inst
                           (when-let [monoid-inst (resolve-basic-instance env "Monoid" type-name-str type-expr)]
                             (e/app* (e/const' (name/from-string "Monoid.toNatPow") [lvl/zero])
                                     type-expr monoid-inst)))]
                     (if pow-inst
                       (e/app* (e/const' (name/from-string "HPow.hPow") [lvl/zero lvl/zero lvl/zero])
                               type-expr nat type-expr
                               (e/app* (e/const' (name/from-string "instHPow") [lvl/zero lvl/zero])
                                       type-expr nat pow-inst)
                               a b)
                       (throw (ex-info (str "No Monoid instance for " type-name-str " (needed for pow)") {}))))
            ;; General binary op with instance resolution
                   (let [op-name (case base-op "+" "HAdd.hAdd" "-" "HSub.hSub"
                                       "*" "HMul.hMul" "/" "HDiv.hDiv")]
                     (build-binop env op-name hop-name basic-class
                                  type-name-str type-expr a b))))

        ;; Equality
               ("=" "Eq")
               (let [args (vec (rest form))
                     [ty lhs rhs] (if (= 3 (count args))
                                    (mapv #(sexp->ansatz env scope depth %) args)
                                    [(e/const' (name/from-string "Nat") [])
                                     (sexp->ansatz env scope depth (nth args 0))
                                     (sexp->ansatz env scope depth (nth args 1))])
              ;; Coerce Nat literals to target type if needed
                     ty-name (when (e/const? ty) (name/->string (e/const-name ty)))
                     coerce (fn [e]
                              (if (and ty-name (not= ty-name "Nat") (e/lit-nat? e))
                                (let [n (e/lit-nat-val e)
                                      inst (cond
                                             (= n 0) (when-let [zi (resolve-basic-instance env "Zero" ty-name ty)]
                                                       (e/app* (e/const' (name/from-string "Zero.toOfNat0") [lvl/zero]) ty zi))
                                             (= n 1) (when-let [oi (resolve-basic-instance env "One" ty-name ty)]
                                                       (e/app* (e/const' (name/from-string "One.toOfNat1") [lvl/zero]) ty oi))
                                             :else nil)]
                                  (if inst
                                    (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero]) ty (e/lit-nat n) inst)
                                    e))
                                e))
                     lhs (coerce lhs)
                     rhs (coerce rhs)]
                 (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) ty lhs rhs))

        ;; Propositions: (le Type a b) → LE.le a b, (lt Type a b) → LT.lt a b
               ("le" "lt")
               (let [type-form (nth form 1)
                     type-expr (sexp->ansatz env scope depth type-form)
                     type-name (when (symbol? (nth form 1)) (str (nth form 1)))
                     a (sexp->ansatz env scope depth (nth form 2))
                     b (sexp->ansatz env scope depth (nth form 3))
              ;; Coerce literals to target type
                     coerce (fn [e]
                              (if (and type-name (not= type-name "Nat") (e/lit-nat? e))
                                (let [n (e/lit-nat-val e)
                                      inst (cond
                                             (= n 0) (when-let [zi (resolve-basic-instance env "Zero" type-name type-expr)]
                                                       (e/app* (e/const' (name/from-string "Zero.toOfNat0") [lvl/zero]) type-expr zi))
                                             (= n 1) (when-let [oi (resolve-basic-instance env "One" type-name type-expr)]
                                                       (e/app* (e/const' (name/from-string "One.toOfNat1") [lvl/zero]) type-expr oi))
                                             :else nil)]
                                  (if inst
                                    (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero]) type-expr (e/lit-nat n) inst)
                                    e))
                                e))
                     a (coerce a) b (coerce b)
              ;; Resolve LE/LT instance
              ;; For Nat: use instLENat/instLTNat directly (Prop-valued, matching Lean 4)
              ;; For other types: use instance synthesis
                     class-name (if (= h "le") "LE" "LT")
                     direct-inst-name (when (= type-name "Nat")
                                        (name/from-string (str "inst" class-name "Nat")))
                     inst (or (when direct-inst-name
                                (when-let [ci (env/lookup env direct-inst-name)]
                                  (e/const' direct-inst-name [])))
                              (try-synthesize-instance env
                                                       (e/app (e/const' (name/from-string class-name) [lvl/zero]) type-expr)))]
                 (if inst
                   (e/app* (e/const' (name/from-string (str class-name "." h)) [lvl/zero])
                           type-expr inst a b)
                   (throw (ex-info (str "No " class-name " instance for " type-name) {}))))

        ;; cond → nested if; do (pure) → its last form.
        ;; (let/let* deferred: needs de-Bruijn-aware value-type inference — task #72.)
               "let*" (compile-let* env scope depth (vec (nth form 1))
                                    (if (> (count form) 3) (cons 'do (drop 2 form)) (nth form 2))
                                    lctx)
               "cond" (sexp->ansatz env scope depth (cond->if (rest form)))
               "do" (sexp->ansatz env scope depth (last form))
               ;; (get m :field) → keyword projection (:field m) — a sound record/structure accessor.
               ;; NB: this alone does NOT enable {:keys […]} destructuring: Clojure's map-destructure
               ;; desugar injects a dynamic seq-normalization preamble (seq?/createAsIfByAssoc) that
               ;; doesn't map to CIC. Full destructuring needs a custom typed desugar (follow-on).
               "get" (if (keyword? (nth form 2 nil))
                       (sexp->ansatz env scope depth (list (nth form 2) (nth form 1)) lctx)
                       (throw (ex-info "get: only keyword field access (on records/structures) is supported"
                                       {:form form})))

        ;; If-then-else (Bool condition → Bool.rec)
        ;; (if cond then-val else-val)
               "if" (let [cond-expr (sexp->ansatz env scope depth (nth form 1))
                          then-expr (sexp->ansatz env scope depth (nth form 2))
                          else-expr (sexp->ansatz env scope depth (nth form 3))
                        ;; Infer the branch type properly under the enclosing binders (open-infer-
                        ;; close). Do NOT guess a default type on failure — that is silently unsound;
                        ;; fail loudly so the user annotates or the code is fixed.
                          ret-type (or (infer-value-type env depth (scope-bvar-types scope depth) then-expr)
                                       (throw (ex-info "if: cannot infer the type of the then-branch"
                                                       {:then (nth form 2)})))]
                    ;; Bool.rec.{u} (motive : Bool → Sort u) (false-case) (true-case) (b : Bool)
                    ;; Note: false case comes FIRST (Bool.false is ctor 0)
                      (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                              (e/lam "_" (e/const' (name/from-string "Bool") []) ret-type :default)
                              else-expr then-expr cond-expr))

        ;; Dependent if-then-else (Prop condition → dite)
        ;; (dif (= Nat n 0) [h] then-val [h] else-val)
        ;; Compiles to: dite (n = 0) (Nat.decEq n 0) (fun h => then-val) (fun h => else-val)
        ;; The h binders give access to the condition/negation in each branch.
               "dif" (let [cond-form (nth form 1)
                           then-var (first (nth form 2))
                           then-body-form (second (nth form 2))
                           else-var (first (nth form 3))
                           else-body-form (second (nth form 3))
                         ;; Compile the Prop condition
                           cond-expr (sexp->ansatz env scope depth cond-form)
                         ;; Infer return type from then-branch (compile with h in scope)
                           then-scope (assoc scope then-var depth)
                           then-expr (sexp->ansatz env then-scope (inc depth) then-body-form)
                           else-scope (assoc scope else-var depth)
                           else-expr (sexp->ansatz env else-scope (inc depth) else-body-form)
                         ;; Build return type
                           tc-dif (ansatz.kernel.TypeChecker. env)
                           _ (.setFuel tc-dif (long config/*default-fuel*))
                           ret-type (try (.inferType tc-dif then-expr)
                                         (catch Exception _ (e/const' (name/from-string "Nat") [])))
                         ;; Build Decidable instance — try synthesizing
                           dec-type (e/app (e/const' (name/from-string "Decidable") []) cond-expr)
                           dec-inst (or (try-synthesize-instance env dec-type)
                                      ;; Fallback: the standard Nat-comparison decidables (Lean's
                                      ;; instances literally are these), since general synthesis can
                                      ;; miss them. Eq Nat → Nat.decEq (3 args: type lhs rhs);
                                      ;; LE.le/LT.lt Nat → Nat.decLe/Nat.decLt (4 args: type inst lhs rhs).
                                        (let [[ch cargs] (e/get-app-fn-args cond-expr)
                                              chn (when (e/const? ch) (name/->string (e/const-name ch)))
                                              nat? (fn [t] (and (e/const? t)
                                                                (= "Nat" (name/->string (e/const-name t)))))]
                                          (cond
                                            (and (= chn "Eq") (= 3 (count cargs)) (nat? (nth cargs 0)))
                                            (e/app* (e/const' (name/from-string "Nat.decEq") [])
                                                    (nth cargs 1) (nth cargs 2))
                                            (and (= chn "LE.le") (= 4 (count cargs)) (nat? (nth cargs 0)))
                                            (e/app* (e/const' (name/from-string "Nat.decLe") [])
                                                    (nth cargs 2) (nth cargs 3))
                                            (and (= chn "LT.lt") (= 4 (count cargs)) (nat? (nth cargs 0)))
                                            (e/app* (e/const' (name/from-string "Nat.decLt") [])
                                                    (nth cargs 2) (nth cargs 3)))))
                           _ (when-not dec-inst
                               (throw (ex-info (str "No Decidable instance for condition") {:cond cond-form})))
                         ;; Not type: ¬ cond = cond → False
                           not-cond (e/app (e/const' (name/from-string "Not") []) cond-expr)
                         ;; Build: dite cond dec-inst (λ h : cond => then) (λ h : ¬cond => else)
                           l1 (lvl/succ lvl/zero)]
                       (e/app* (e/const' (name/from-string "dite") [l1])
                               ret-type cond-expr dec-inst
                               (e/lam (str then-var) cond-expr then-expr :default)
                               (e/lam (str else-var) not-cond else-expr :default)))

        ;; Binders
               "forall" (build-telescope env scope depth
                                         (partition 2 (remove #{:-} (nth form 1))) (nth form 2) e/forall')
               ;; `lam` is ansatz's native lambda; `fn` (a Clojure macro) macroexpands to `fn*`.
               ;; Both accept metadata-typed binders (parse-params handles metadata / :- / positional).
               "lam" (build-telescope env scope depth (parse-params (nth form 1)) (nth form 2) e/lam)
               ;; (fn* [name?] ([params] body…) …) — single-arity only (a kernel lambda has one arity);
               ;; metadata survives the fn macroexpansion, so ^Nat / ^{:- T} on params just work.
               "fn*" (let [cls (rest form)
                           cls (if (symbol? (first cls)) (rest cls) cls)   ; skip optional self-name
                           arities (filter #(and (sequential? %) (vector? (first %))) cls)]
                       (if (= 1 (count arities))
                         (let [[params & body] (first arities)
                               body-form (if (> (count body) 1) (cons 'do body) (first body))]
                           (build-telescope env scope depth (parse-params params) body-form e/lam))
                         (throw (ex-info (str "fn: only single-arity lambdas elaborate to kernel "
                                              "terms (multi-arity / variadic not supported)")
                                         {:form form}))))
               ;; Function-type arrow. `=>` is THE arrow (any position); `->` is always Clojure
               ;; threading and never reaches here (it is macroexpanded).
               ("=>" "arrow") (e/arrow (sexp->ansatz env scope depth (nth form 1))
                                       (sexp->ansatz env scope (inc depth) (nth form 2)))

        ;; Logic
               "And" (e/app* (e/const' (name/from-string "And") [])
                             (sexp->ansatz env scope depth (nth form 1))
                             (sexp->ansatz env scope depth (nth form 2)))
               "Or"  (e/app* (e/const' (name/from-string "Or") [])
                             (sexp->ansatz env scope depth (nth form 1))
                             (sexp->ansatz env scope depth (nth form 2)))
               "Exists" (e/app* (e/const' (name/from-string "Exists") [(lvl/succ lvl/zero)])
                                (sexp->ansatz env scope depth (nth form 1))
                                (sexp->ansatz env scope depth (nth form 2)))

        ;; cons/nil for lists — infer element type via auto-elaborate
        ;; (Lean 4: List.cons.{u} : {α : Type u} → α → List α → List α)
               "cons" (let [x (sexp->ansatz env scope depth (nth form 1))
                            s-raw (sexp->ansatz env scope depth (nth form 2))
                            head-fn (e/const' (name/from-string "List.cons") [lvl/zero])
                            ci (env/lookup env (name/from-string "List.cons"))
                            bvar-tys (when (and (seq scope) *scope-types*)
                                       (into {} (keep (fn [[sym d]]
                                                        (when-let [ty (get *scope-types* sym)]
                                                          [(- depth 1 d) ty]))
                                                      scope)))
                          ;; Infer element type from x
                            elem-type (get-arg-type env bvar-tys x)
                          ;; Fix nil: if s-raw is List.nil with wrong type, re-create with inferred type
                            s (if (and elem-type (e/app? s-raw))
                                (let [[sh sa] (e/get-app-fn-args s-raw)]
                                  (if (and (e/const? sh)
                                           (= "List.nil" (name/->string (e/const-name sh)))
                                           (= 1 (count sa))
                                           (not (.equals (first sa) elem-type)))
                                    (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) elem-type)
                                    s-raw))
                                s-raw)]
                        (if (and ci elem-type)
                        ;; Use inferred type directly (more reliable than auto-elaborate for this case)
                          (e/app* head-fn elem-type x s)
                          (if ci
                            (auto-elaborate env head-fn (.type ^ansatz.kernel.ConstantInfo ci) [x s]
                                            :bvar-types bvar-tys)
                            (e/app* head-fn (e/const' (name/from-string "Nat") []) x s))))
               "length" (let [nat (e/const' (name/from-string "Nat") [])]
                          (e/app* (e/const' (name/from-string "List.length") [lvl/zero]) nat
                                  (sexp->ansatz env scope depth (nth form 1))))

        ;; Pattern matching on inductives → delegates to surface/match.clj
        ;; Uses Lean 4's open/close pattern: convert outer bvars to fvars,
        ;; run fvar-based match compiler, abstract fvars back to bvars.
               "match"
               (let [scrutinee-form (nth form 1)
                     type-form (nth form 2)
                     ret-type-form (nth form 3)
                     cases (drop 4 form)
              ;; Step 1: OPEN — create fvars for all outer-scope bvars,
              ;; AND include any fvars from an enclosing match (via lctx).
              ;; This mirrors Lean 4's forallTelescope.
              ;; Base fvar ID: must not collide with any existing fvars from
              ;; enclosing matches (via lctx). Derive from max existing ID.
                     outer-fvar-base (if (and lctx (seq lctx))
                                       (+ 1000 (reduce max 3000000 (keys lctx)))
                                       3000000)
              ;; Fvars from bvar scope (function parameters)
                     bvar-fvars (into {} (map (fn [[sym bvar-depth]]
                                                (let [fid (+ outer-fvar-base bvar-depth)]
                                                  [sym {:fvar-id fid
                                                        :bvar-depth bvar-depth
                                                        :fvar (e/fvar fid)}]))
                                              scope))
              ;; Fvars from lctx (enclosing match fields, hypothesis context)
                     lctx-fvars (when lctx
                                  (into {} (map (fn [[fid {:keys [name type]}]]
                                                  [(symbol name) {:fvar-id fid
                                                                  :bvar-depth nil  ;; no bvar to abstract
                                                                  :fvar (e/fvar fid)
                                                                  :type type}])
                                                lctx)))
                     outer-fvars (merge lctx-fvars bvar-fvars)
              ;; Build substitution: replace each bvar with its fvar
              ;; We need to instantiate from innermost (highest depth) outward
                     open-expr (fn [expr]
                                 (reduce (fn [e [sym {:keys [bvar-depth fvar]}]]
                                    ;; Replace bvar at this depth with the fvar
                                    ;; We process from innermost to outermost
                                           e)
                                         expr
                                  ;; Actually, a simpler approach: walk the expr once
                                  ;; and replace any bvar whose index maps to an outer scope entry
                                         (sort-by (fn [[_ v]] (- (:bvar-depth v))) outer-fvars)))
              ;; Simpler: compile with an lctx that maps outer names to fvars,
              ;; then the match compiler's elab-fn produces fvars for all variables.
              ;; Build outer-lctx with TYPES for every fvar.
              ;; Types come from: *scope-types* (function params), incoming lctx
              ;; (enclosing match fields/IHs), or nil (if truly unknown).
              ;; Lean 4 invariant: every fvar MUST have a type in LocalContext.
                     outer-lctx (into {} (map (fn [[sym {:keys [fvar-id bvar-depth]}]]
                                                (let [;; Try *scope-types* first (function params)
                                                      ftype (or (get *scope-types* sym)
                                                         ;; Then incoming lctx (enclosing match)
                                                                (when lctx
                                                                  (:type (get lctx fvar-id))))]
                                                  [fvar-id {:name (str sym) :type ftype :tag :local}]))
                                              outer-fvars))
              ;; Compile scrutinee and type with outer fvars visible
                     scrutinee (sexp->ansatz env {} 0 scrutinee-form outer-lctx)
                     type-expr (sexp->ansatz env {} 0 type-form outer-lctx)
                     type-whnf (try (red/whnf-no-delta env type-expr) (catch Exception _ type-expr))
              ;; Build elaboration state — all scope entries are fvar-based.
              ;; Register outer fvars in the tc's local context with their types.
              ;; This is critical: the match compiler may call tc/infer-type on
              ;; expressions containing these fvars.
                     base-tc (tc/mk-tc-state env)
                     tc-with-outer (reduce
                                    (fn [tc-st [sym {:keys [fvar-id type]}]]
                                      (let [;; Type from: entry itself, *scope-types*, or incoming lctx
                                            ftype (or type
                                                      (get *scope-types* sym)
                                                      (when lctx (:type (get lctx fvar-id))))]
                                        (if ftype
                                          (update tc-st :lctx
                                                  red/lctx-add-local fvar-id (str sym) ftype)
                                          tc-st)))
                                    base-tc outer-fvars)
                     est {:env env
                          :tc tc-with-outer
                          :next-id (atom (+ outer-fvar-base (count scope) 1000))
                          :mctx (atom {})
                          :level-mctx (atom {})
                          :scope (into {} (map (fn [[sym {:keys [fvar-id type]}]]
                                                 (let [ftype (or type (get *scope-types* sym))]
                                                   [sym {:fvar-id fvar-id :type ftype}]))
                                               outer-fvars))
                          :depth 0}
              ;; Adapter: compile RHS expressions.
              ;; Match-field fvars are in est's :scope — produce fvars for those.
              ;; Outer-scope bvar entries use the original scope+depth (shifted
              ;; by the number of field+IH lambdas the match compiler creates).
              ;; We pass the match fields as lctx so sexp->ansatz produces fvars.
                     elab-fn (fn elab-adapter [est sexpr]
                               (let [;; Build lctx from ALL fvar entries (outer + match fields)
                                     all-lctx (into outer-lctx
                                                    (map (fn [[sym {:keys [fvar-id type]}]]
                                                           [fvar-id {:name (str sym) :type type
                                                                     :tag :local}])
                                                         (:scope est)))]
                                 (binding [*current-lctx* all-lctx]
                                   (sexp->ansatz env {} 0 sexpr all-lctx))))
              ;; Resolve the inductive type name for constructor qualification
                     type-expr-for-name (sexp->ansatz env {} 0 type-form outer-lctx)
                     [type-head-for-name _] (e/get-app-fn-args type-expr-for-name)
                     ind-name-str (when (e/const? type-head-for-name)
                                    (name/->string (e/const-name type-head-for-name)))
              ;; Convert case forms — qualify constructor names with inductive type
                     alt-sexprs (mapv (fn [case-form]
                                        (let [ctor-raw (first case-form)
                                       ;; Qualify: leaf → IndType.leaf, true → Bool.true
                                              ctor-sym (cond
                                                         (true? ctor-raw) 'Bool.true
                                                         (false? ctor-raw) 'Bool.false
                                                         (nil? ctor-raw) (symbol (str ind-name-str ".nil"))
                                                  ;; If already qualified (has dot), keep as-is
                                                         (and (symbol? ctor-raw)
                                                              (.contains (str ctor-raw) "."))
                                                         ctor-raw
                                                  ;; Otherwise qualify with inductive name
                                                         :else (symbol (str ind-name-str "." ctor-raw)))
                                              has-fields (and (> (count case-form) 2)
                                                              (vector? (second case-form)))
                                              field-names (if has-fields (second case-form) [])
                                              body-form (if has-fields (nth case-form 2)
                                                            (second case-form))
                                              pat (if (seq field-names)
                                                    (cons ctor-sym field-names)
                                                    ctor-sym)]
                                          [pat body-form]))
                                      cases)
                     alts (mapv (fn [[pat-sexpr rhs-sexpr]]
                                  {:pattern (surface-match/parse-pattern env pat-sexpr)
                                   :rhs-sexpr rhs-sexpr})
                                alt-sexprs)
              ;; Step 2: RUN — compile match with fvar-based expressions
                     result (#'surface-match/compile-match-term est env elab-fn scrutinee type-whnf alts)
              ;; Step 3: CLOSE — abstract bvar-based outer fvars back to bvars.
              ;; Uses abstract-many for correct multi-fvar abstraction
              ;; (sequential abstract1 doesn't shift existing bvars).
              ;; Order: outermost to innermost (matching build-telescope).
              ;; fv-ids[0] = outermost → highest bvar index.
              ;; Lctx fvars (from enclosing match) stay as fvars.
                     bvar-entries (sort-by (fn [[_ v]] (or (:bvar-depth v) -1))
                                           (filter (fn [[_ v]] (:bvar-depth v)) outer-fvars))
                     fv-ids (mapv (fn [[_ {:keys [fvar-id]}]] fvar-id) bvar-entries)
                     result (e/abstract-many result fv-ids)]
                 result)

        ;; Default: auto-elaborating application
        ;; Walk the function's forall telescope, inserting implicit and
        ;; instance-implicit arguments automatically.
               (let [compiled (mapv #(sexp->ansatz env scope depth %) form)
                     head-fn (first compiled)
                     user-args (rest compiled)]
                 (if-let [^ConstantInfo ci (when (e/const? head-fn)
                                             (env/lookup env (e/const-name head-fn)))]
                 ;; Build bvar-types map so auto-elaborate can infer types of bound vars
                   (let [bvar-tys (when (and (seq scope) (seq *scope-types*))
                                    (into {} (keep (fn [[sym d]]
                                                     (when-let [ty (get *scope-types* sym)]
                                                       [(- depth 1 d) ty]))
                                                   scope)))]
                     (auto-elaborate env head-fn (.type ci) (vec user-args)
                                     :bvar-types bvar-tys))
            ;; Not a known constant — just apply directly
                   (reduce e/app compiled)))))))

       :else (throw (ex-info (str "Cannot compile: " form) {:form form}))))))

;; ============================================================
;; Ansatz Expr → Clojure form compiler
;; ============================================================

(clojure.core/defn ansatz->clj
  "Compile Ansatz Expr to Clojure form for eval."
  [env expr names]
  (cond
    (e/lit-nat? expr) (e/lit-nat-val expr)
    (e/lit-str? expr) (e/lit-str-val expr)
    (e/bvar? expr) (let [i (e/bvar-idx expr)]
                     (if (< i (count names))
                       (symbol (nth names (- (count names) i 1)))
                       (symbol (str "_" i))))
    (e/lam? expr) (let [n (or (e/lam-name expr) "x")]
                    (list 'fn [(symbol n)]
                          (ansatz->clj env (e/lam-body expr) (conj names n))))
    (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)]
      (if (e/const? head)
        (let [h (name/->string (e/const-name head))
              ca (mapv #(ansatz->clj env % names) args)]
          (case h
            ;; dite α cond dec then-fn else-fn → (if bool-cond then else)
            ;; then-fn = λ h => body, else-fn = λ h => body (h is proof, erased at runtime)
            "dite"
            (let [;; args: [α, cond, dec-inst, then-fn, else-fn]
                  then-fn (nth args 3)   ;; Ansatz lambda: λ h => then-body
                  else-fn (nth args 4)   ;; Ansatz lambda: λ h => else-body
                  ;; Peel lambda, compile body (the h arg is a proof — not used at runtime)
                  then-body (if (e/lam? then-fn)
                              (ansatz->clj env (e/lam-body then-fn) (conj names "_h"))
                              (nth ca 3))
                  else-body (if (e/lam? else-fn)
                              (ansatz->clj env (e/lam-body else-fn) (conj names "_h"))
                              (nth ca 4))
                  ;; Build runtime condition from the Decidable instance.
                  ;; Decidable.decide returns Bool; or for Nat.decEq a b, use ==
                  dec-expr (nth args 2) ;; Ansatz expr for Decidable instance
                  [dec-head dec-args] (e/get-app-fn-args dec-expr)
                  bool-cond (if (and (e/const? dec-head)
                                     (= "Nat.decEq" (name/->string (e/const-name dec-head))))
                              ;; Nat.decEq a b → (== a b) at runtime
                              (list '== (ansatz->clj env (nth dec-args 0) names)
                                    (ansatz->clj env (nth dec-args 1) names))
                              ;; Generic: compile the decidable instance (may not work for all cases)
                              (nth ca 2))]
              (list 'if bool-cond then-body else-body))
            ;; WellFounded.Nat.fix α motive measure F x → letfn recursive call
            ;; F = λ x (λ IH body) — compile body with IH→self-call, dropping proof args
            "WellFounded.Nat.fix"
            (if (= 5 (count ca))
              ;; Full application: WF.Nat.fix α motive measure F x
              (let [f-expr (nth args 3) ;; F as Ansatz Expr
                    x-arg (nth ca 4)    ;; compiled x
                    self-sym (gensym "wf_")
                    ;; F = λ x. λ IH. body
                    ;; Peel two lambdas
                    f-body-1 (when (e/lam? f-expr) (e/lam-body f-expr))
                    f-body-2 (when (and f-body-1 (e/lam? f-body-1)) (e/lam-body f-body-1))
                    x-name (when (e/lam? f-expr) (or (e/lam-name f-expr) "x"))
                    ih-name (when (and f-body-1 (e/lam? f-body-1))
                              (or (e/lam-name f-body-1) "IH"))
                    compiled-body (when f-body-2
                                    (ansatz->clj env f-body-2
                                                 (conj names x-name ih-name)))
                    ;; Replace IH calls: (IH arg proof) → (self arg)
                    ;; In compiled form, IH is a symbol. Calls look like ((IH arg) proof).
                    ;; We need to replace (IH-sym arg proof) patterns with (self arg).
                    ih-sym (symbol ih-name)
                    replace-ih (fn replace-ih [form]
                                 (cond
                                   ;; ((IH y) proof) → (self y)
                                   (and (seq? form) (= 2 (count form))
                                        (seq? (first form)) (= 2 (count (first form)))
                                        (= ih-sym (ffirst form)))
                                   (list self-sym (second (first form)))
                                   (seq? form) (apply list (map replace-ih form))
                                   (vector? form) (mapv replace-ih form)
                                   :else form))
                    final-body (replace-ih compiled-body)]
                (list 'letfn [(list self-sym [(symbol x-name)] final-body)]
                      (list self-sym x-arg)))
              ;; Partial application (shouldn't happen normally)
              (list 'apply (ansatz->clj env head names) ca))
            "HAdd.hAdd" (list '+ (nth ca 4) (nth ca 5))
            "HMul.hMul" (list '* (nth ca 4) (nth ca 5))
            "HSub.hSub" (list 'max 0 (list '- (nth ca 4) (nth ca 5)))
            "HDiv.hDiv" (list 'quot (nth ca 4) (nth ca 5))
            "HPow.hPow" (list 'long (list 'Math/pow (nth ca 4) (nth ca 5)))
            "Nat.add" (list '+ (nth ca 0) (nth ca 1))
            "Nat.sub" (list 'max 0 (list '- (nth ca 0) (nth ca 1)))  ; truncated Nat subtraction
            "Nat.mul" (list '* (nth ca 0) (nth ca 1))
            "Nat.div" (list 'quot (nth ca 0) (nth ca 1))
            "Nat.pow" (list 'long (list 'Math/pow (nth ca 0) (nth ca 1)))
            "Nat.succ" (list 'inc (nth ca 0))
            "Bool.true" true
            "Bool.false" false
            "Nat.zero" 0
            "ite" (list 'if (nth ca 1) (nth ca 3) (nth ca 4))
            ;; Nat comparison → Clojure primitives
            "Nat.blt" (list '< (nth ca 0) (nth ca 1))
            "Nat.ble" (list '<= (nth ca 0) (nth ca 1))
            "Nat.beq" (list '== (nth ca 0) (nth ca 1))
            ;; List operations → Clojure persistent list
            "List.cons" (list 'clojure.core/cons (nth ca 1) (nth ca 2))
            "List.nil" nil
            "List.length" (list 'count (nth ca 1))
            ;; Constructor application
            ;; For structures (defrecord): use ->RecordName constructor
            ;; For other inductives: tagged vector [field1 field2 ...]
            (if-let [ctor-ci (when-let [ci (env/lookup env (e/const-name head))]
                               (when (.isCtor ^ConstantInfo ci) ci))]
              (let [np (.numParams ctor-ci)
                    nf (.numFields ctor-ci)
                    fields (subvec ca np (+ np nf))
                    ;; Check if this is a structure with a defrecord
                    ind-name (subs h 0 (max 0 (- (count h) (count (name/->string (.name ctor-ci)))
                                                 -1 (count h))))
                    ;; Get the inductive name from the ctor name: T.mk → T
                    ctor-str (name/->string (.name ctor-ci))
                    dot-idx (.lastIndexOf ^String ctor-str ".")
                    struct-name (when (pos? dot-idx) (subs ctor-str 0 dot-idx))
                    struct-info (when struct-name (get @structure-registry struct-name))]
                (cond
                  ;; Structure with defrecord: use ->RecordName constructor
                  (and struct-info (= nf (count (:fields struct-info))))
                  (apply list (:ctor-sym struct-info) fields)
                  ;; 0-field ctor: use index for enum dispatch
                  (zero? nf)
                  (let [cidx (.cidx ctor-ci)]
                    (if (zero? cidx) nil cidx))
                  ;; Default: tagged vector
                  :else (vec fields)))
              ;; Generic recursor compilation: *.rec → case dispatch with recursion
              (if-let [rec-ci (when (.endsWith ^String h ".rec")
                                (env/lookup env (e/const-name head)))]
                (when (.isRecursor ^ConstantInfo rec-ci)
                  (let [np (.numParams rec-ci)
                        nm (.numMotives rec-ci)
                        nmin (.numMinors rec-ci)
                        minor-start (+ np nm)
                        major-idx (+ minor-start nmin)
                        major (nth ca major-idx)
                        rules (.rules rec-ci)
                      ;; Determine which fields are recursive per constructor
                        ind-name-str (subs h 0 (- (count h) 4)) ;; remove ".rec"
                        ind-ci (env/lookup env (name/from-string ind-name-str))
                      ;; Build a letfn with self-recursive function
                        self-sym (gensym "rec_")
                        ;; Unique prefix for field names to avoid shadowing in nested matches
                        field-prefix (str "f" (gensym "") "_")
                        clauses
                        (map-indexed
                         (fn [i ^ansatz.kernel.ConstantInfo$RecursorRule rule]
                           (let [nf (.nfields rule)
                                 minor (nth ca (+ minor-start i))
                                 minor-ansatz-expr (nth args (+ minor-start i))
                                 ctor-name (.ctor rule)
                                 ctor-ci (env/lookup env ctor-name)
                                ;; Find recursive field indices
                                 rec-indices
                                 (when (.isRec ind-ci)
                                   (let [ct (.type ctor-ci)]
                                     (loop [ty ct skip (.numParams ctor-ci) j 0 acc []]
                                       (if (or (not (e/forall? ty)) (>= j nf))
                                         acc
                                         (if (pos? skip)
                                           (recur (e/forall-body ty) (dec skip) j acc)
                                           (let [ft (e/forall-type ty)
                                                 is-rec (ansatz.inductive/occurs-in?
                                                         ft (name/from-string ind-name-str))]
                                             (recur (e/forall-body ty) 0 (inc j)
                                                    (if is-rec (conj acc j) acc))))))))
                                 field-syms (mapv #(symbol (str field-prefix %)) (range nf))
                                 ih-syms (mapv #(symbol (str "ih" (gensym "") "_" %)) (or rec-indices []))]
                             {:idx i :nfields nf :minor minor :minor-ansatz minor-ansatz-expr
                              :field-syms field-syms
                              :rec-indices (or rec-indices []) :ih-syms ih-syms}))
                         rules)]
                  ;; Generate case dispatch
                    (let [t-sym (gensym "t_")
                          all-zero (every? #(zero? (:nfields %)) clauses)
                          has-rec (some #(seq (:rec-indices %)) clauses)
                          apply-minor (fn [clause args]
                                        (reduce (fn [f a] (list f a))
                                                (:minor clause) args))
                          body
                          (cond
                          ;; Enum: all ctors have 0 fields (Bool, Color, etc.)
                            (and all-zero (= 2 (count clauses)))
                          ;; Bool-like: (if value minor_1 minor_0)
                          ;; ctor 0 = falsy (nil/false), ctor 1 = truthy
                            (list 'if t-sym
                                  (:minor (second clauses))
                                  (:minor (first clauses)))

                            all-zero  ;; 3+ ctor enum
                            (list* 'case t-sym
                                   (mapcat (fn [{:keys [idx minor]}] [idx minor])
                                           clauses))

                          ;; Nat.rec: Nat is native longs, not nil/vector
                            (and (= ind-name-str "Nat")
                                 (= 2 (count clauses))
                                 (zero? (:nfields (first clauses))))
                            (let [leaf-c (first clauses)
                                  node-c (second clauses)
                                  pred-sym (first (:field-syms node-c))
                                ;; Nat.succ has 1 field: predecessor
                                  bindings [pred-sym (list 'dec t-sym)]
                                  minor-ansatz (:minor-ansatz node-c)
                                  n-ih (count (:rec-indices node-c))
                                  all-names (into (mapv str (:field-syms node-c))
                                                  (mapv str (:ih-syms node-c)))
                                  minor-body (loop [e minor-ansatz n (+ 1 n-ih)]
                                               (if (and (pos? n) (e/lam? e))
                                                 (recur (e/lam-body e) (dec n))
                                                 e))
                                  compiled-body (ansatz->clj env minor-body
                                                             (into names all-names))
                                  ih-replacements
                                  (into {} (map (fn [j ri]
                                                  [(nth (:ih-syms node-c) j)
                                                   (list self-sym (nth (:field-syms node-c) ri))])
                                                (range n-ih) (:rec-indices node-c)))
                                  major-sym (when (symbol? major) major)
                                  inline-all (fn inline-all [form]
                                               (cond
                                                 (and (symbol? form) (contains? ih-replacements form))
                                                 (get ih-replacements form)
                                                 (and major-sym (symbol? form) (= form major-sym))
                                                 t-sym
                                                 (seq? form) (apply list (map inline-all form))
                                                 (vector? form) (mapv inline-all form)
                                                 :else form))
                                  node-body (inline-all compiled-body)]
                              (list 'if (list 'zero? t-sym)
                                    (:minor leaf-c)
                                    (list 'let bindings node-body)))

                          ;; Leaf + node: first ctor 0 fields, others have fields
                            (and (= 2 (count clauses))
                                 (zero? (:nfields (first clauses))))
                            (let [leaf-c (first clauses)
                                  node-c (second clauses)
                                  nf (:nfields node-c)
                                ;; Field bindings: [color (nth t 0) left (nth t 1) ...]
                                ;; For List: use first/rest instead of nth (native seq interop)
                                ;; Also bind the discriminant name to t-sym so that
                                ;; references to the matched value inside the body
                                ;; see the current node, not the outer parameter.
                                  is-list (= ind-name-str "List")
                                  bindings (vec (mapcat (fn [i]
                                                          [(nth (:field-syms node-c) i)
                                                           (if is-list
                                                             (case (int i)
                                                               0 (list 'first t-sym)
                                                               1 (list 'rest t-sym))
                                                             (list 'nth t-sym i))])
                                                        (range nf)))
                                ;; Unwrap minor Ansatz lambdas to get the body
                                ;; Then compile body with field names + IH inlined as (rec field)
                                  minor-ansatz (:minor-ansatz node-c)
                                ;; Unwrap nf + n-ih lambdas
                                  n-ih (count (:rec-indices node-c))
                                  all-names (into (mapv str (:field-syms node-c))
                                                  (mapv str (:ih-syms node-c)))
                                  minor-body (loop [e minor-ansatz n (+ nf n-ih)]
                                               (if (and (pos? n) (e/lam? e))
                                                 (recur (e/lam-body e) (dec n))
                                                 e))
                                ;; Compile body with names for fields + IH symbols
                                  compiled-body (ansatz->clj env minor-body
                                                             (into names all-names))
                                ;; Replace IH symbols with inline recursive calls
                                ;; ih_sym → (self_fn field_sym) — lazy, only evaluated when needed
                                  ih-replacements
                                  (into {} (map (fn [j ri]
                                                  [(nth (:ih-syms node-c) j)
                                                   (list self-sym (nth (:field-syms node-c) ri))])
                                                (range n-ih) (:rec-indices node-c)))
                                  ;; Replace major-premise references with t-sym.
                                  ;; When the body references the matched value (e.g., `l`
                                  ;; in `(cons x l)` inside a match on `l`), it should
                                  ;; refer to the current node in the recursion, not the
                                  ;; outer function parameter.
                                  major-sym (when (symbol? major) major)
                                  inline-all (fn inline-all [form]
                                               (cond
                                                 (and (symbol? form) (contains? ih-replacements form))
                                                 (get ih-replacements form)
                                                 (and major-sym (symbol? form) (= form major-sym))
                                                 t-sym
                                                 (seq? form) (apply list (map inline-all form))
                                                 (vector? form) (mapv inline-all form)
                                                 :else form))
                                  node-body (inline-all compiled-body)]
                              ;; For List: use (not (seq t)) since (rest (cons x nil)) = ()
                              (list 'if (if is-list
                                          (list 'not (list 'seq t-sym))
                                          (list 'nil? t-sym))
                                    (:minor leaf-c)
                                    (list 'let bindings node-body)))

                            :else
                            (list 'throw (list 'ex-info "unsupported rec pattern" {})))]
                    ;; Wrap in letfn only if recursive, otherwise just inline
                      (let [rec-result
                            (if has-rec
                              (list 'letfn [(list self-sym [t-sym] body)]
                                    (list self-sym major))
                              ;; Non-recursive: just apply directly
                              (list 'let [t-sym major] body))
                            ;; Extra args beyond major? Apply them (fuel-based WF pattern).
                            extra-args (subvec ca (inc major-idx))]
                        (reduce (fn [f a] (list f a)) rec-result extra-args)))))
            ;; User-defined function: arity-aware compilation (Lean 4 FAP/PAP).
            ;; Check the arity registry to determine call style.
                (if-let [cg (get @codegen-registry h)]
                  ;; Codegen seam: runtime-registered lowering for heads ansatz doesn't know
                  ;; natively (e.g. List.map → wandler's amapl). Consulted before the user-fn fallback.
                  (cg env expr names)
                  (let [{:keys [arity erased]} (get @arity-registry h)]
                    (if (and arity (> arity 1) (>= (count ca) (+ arity erased)))
                      ;; FAP (full application): flat multi-arg call, skip erased prefix
                      (let [rt-args (subvec ca erased (+ erased arity))]
                        (apply list (symbol h) rt-args))
                      ;; Curried (unknown arity, single-arg, or partial application)
                      (reduce (fn [f a] (list f a)) (symbol h) ca))))))))
        (let [compiled (mapv #(ansatz->clj env % names) (cons head args))]
          (reduce (fn [f a] (list f a)) compiled))))
    (e/const? expr) (let [cn (name/->string (e/const-name expr))]
                      (case cn
                        "Nat.zero" 0 "Bool.true" true "Bool.false" false
                        ;; Check if it's a constructor
                        (if-let [ci (env/lookup env (e/const-name expr))]
                          (if (.isCtor ^ConstantInfo ci)
                            (if (zero? (.numFields ci))
                              ;; 0-field ctor: use index for enum dispatch.
                              ;; ctor 0 = nil (falsy), ctor 1+ = index (truthy).
                              ;; This matches the (if v ctor1 ctor0) pattern.
                              (let [cidx (.cidx ci)]
                                (if (zero? cidx) nil cidx))
                              (symbol cn))
                            (symbol cn))
                          (symbol cn))))
    ;; Projection: Expr.proj type-name idx struct
    ;; For structures with defrecord: keyword access (:field-name struct)
    ;; For others: (nth struct idx)
    (e/proj? expr)
    (let [type-name-str (name/->string (e/proj-type-name expr))
          idx (e/proj-idx expr)
          struct-expr (ansatz->clj env (e/proj-struct expr) names)
          struct-info (get @structure-registry type-name-str)]
      (if (and struct-info (< idx (count (:fields struct-info))))
        ;; Structure with defrecord: keyword access
        (list (keyword (nth (:fields struct-info) idx)) struct-expr)
        ;; Fallback: nth on vector
        (list 'nth struct-expr idx)))
    (e/let? expr) (let [n (or (e/let-name expr) "x")]
                    (list 'let [(symbol n) (ansatz->clj env (e/let-value expr) names)]
                          (ansatz->clj env (e/let-body expr) (conj names n))))
    :else expr))

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
  "Register a custom elaboration form for sexp->ansatz.

   Example:
     (a/register-elaborator! 'my-form
       (fn [env scope depth args lctx]
         ;; args: the arguments after the form name
         ;; Return: an Expr (kernel expression)
         (let [a (sexp->ansatz env scope depth (first args) lctx)]
           (e/app (e/const' (name/from-string \"MyFn\") []) a))))

   Then use in definitions:
     (a/defn ^Nat f [^Nat x] (my-form x))"
  [name f]
  (swap! elaborator-registry assoc name f))

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

(def ^:private builtin-tactics
  {'rfl        (fn [ps _] (basic/rfl ps))
   'assumption (fn [ps _] (basic/assumption ps))
   'constructor (fn [ps _] (basic/constructor ps))
   'exfalso   (fn [ps _] (basic/exfalso ps))
   'left      (fn [ps _] (basic/left ps))
   'right     (fn [ps _] (basic/right ps))
   'exact?    (fn [ps _] (basic/exact? ps))
   'omega     (fn [ps _] (omega/omega ps))
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
                      mid (sexp->ansatz (:env ps) {} 0 (first args) lctx)
                      h1-term (sexp->ansatz (:env ps) {} 0 (second args) lctx)
                      h2-term (sexp->ansatz (:env ps) {} 0 (nth args 2) lctx)
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
                ;; (have name type) — introduces a have goal
                ;; Pass local context so hypothesis names resolve as fvars
                (let [hyp-name (str (first args))
                      g (proof/current-goal ps)
                      hyp-type (sexp->ansatz (:env ps) {} 0 (second args) (:lctx g))]
                  (basic/have-tac ps hyp-name hyp-type)))
   'simp      (fn [ps args] (if (seq args) (simp/simp ps (vec args)) (simp/simp ps)))
   'simp_all  (fn [ps args] (if (seq args) (simp/simp-all ps (vec args)) (simp/simp-all ps)))
   'intro     (fn [ps args] (if (seq args) (basic/intros ps (mapv str args)) (basic/intro ps)))
   'intros    (fn [ps args] (basic/intros ps (mapv str args)))
   'apply     (fn [ps args]
                (let [arg (first args)
                      g (proof/current-goal ps)
                      ;; Compile term with local context for hypothesis references
                      term (sexp->ansatz (:env ps) {} 0 arg (:lctx g))]
                  (basic/apply-tac ps term)))
   'rewrite   (fn [ps args]
                (let [nm (str (first args))
                      ;; When names shadow, prefer the most recently allocated fvar (highest ID)
                      fid (reduce (fn [best [id d]]
                                    (if (and (= nm (:name d))
                                             (or (nil? best) (> (long id) (long best))))
                                      id best))
                                  nil (:lctx (proof/current-goal ps)))]
                  (basic/rewrite ps (e/fvar fid))))
   'cases     (fn [ps args]
                (let [nm (str (first args))
                      fid (reduce (fn [best [id d]]
                                    (if (and (= nm (:name d))
                                             (or (nil? best) (> (long id) (long best))))
                                      id best))
                                  nil (:lctx (proof/current-goal ps)))]
                  (basic/cases ps fid)))
   'induction (fn [ps args]
                (let [nm (str (first args))
                      fid (reduce (fn [best [id d]]
                                    (if (and (= nm (:name d))
                                             (or (nil? best) (> (long id) (long best))))
                                      id best))
                                  nil (:lctx (proof/current-goal ps)))]
                  (basic/induction ps fid)))
   'whnf      (fn [ps _args] (basic/whnf-goal ps))
   'unfold    (fn [ps args]
                (basic/unfold-in-goal ps (str (first args))))
   'by_cases  (fn [ps args]
                (let [g (proof/current-goal ps)
                      cond-expr (sexp->ansatz (:env ps) {} 0 (first args) (:lctx g))]
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
   'solve_by_elim (fn [ps _args] (basic/solve-by-elim ps))
   'split_ifs (fn [ps _args] (basic/split-ifs ps))
   'revert    (fn [ps args]
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/revert ps fid)))})

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
;; Well-Founded Recursion (following Lean 4's WellFounded.Nat.fix)
;; ============================================================

(clojure.core/defn- replace-rec-calls
  "Walk expr, replacing calls to fn-name with IH applications.
   For fuel-based recursion: fn-name(arg) → ih(arg), no proof args.

   ih-depth: de Bruijn depth of the IH bvar relative to the current position.
   fn-name: Name of the function being defined.
   fn-arity: number of user-visible args the function takes.
   discr-expr: unused in fuel-based approach (kept for API compatibility)."
  [expr fn-name fn-arity ih-depth discr-expr]
  (let [walk
        (fn walk [e depth-offset discr]
          (cond
            ;; Application: check for recursive call or recursor
            (e/app? e)
            (let [[head args] (e/get-app-fn-args e)]
              (cond
                ;; Found a recursive call: replace with IH(arg, proof)
                (and (e/const? head)
                     (= (name/->string (e/const-name head))
                        (name/->string fn-name))
                     (= fn-arity (count args)))
                ;; Fuel-based: replace fn-name(args...) with ih(args...), no proof needed
                (let [walked-args (mapv #(walk % depth-offset discr) args)
                      ih-ref (e/bvar (+ ih-depth depth-offset))]
                  (reduce e/app ih-ref walked-args))

                ;; Detect Nat.rec application and specialize IH per branch
                ;; Generic application: walk children
                :else
                (reduce e/app (walk head depth-offset discr)
                        (mapv #(walk % depth-offset discr) args))))
            ;; Lambda: descend, incrementing depth
            (e/lam? e)
            (e/lam (e/lam-name e) (walk (e/lam-type e) depth-offset discr)
                   (walk (e/lam-body e) (inc depth-offset) discr)
                   (e/lam-info e))
            ;; Forall: descend
            (e/forall? e)
            (e/forall' (e/forall-name e) (walk (e/forall-type e) depth-offset discr)
                       (walk (e/forall-body e) (inc depth-offset) discr)
                       (e/forall-info e))
            ;; Let: descend
            (e/let? e)
            (e/let' (e/let-name e) (walk (e/let-type e) depth-offset discr)
                    (walk (e/let-value e) depth-offset discr)
                    (walk (e/let-body e) (inc depth-offset) discr))
            ;; Leaf nodes
            :else e))]
    (walk expr 0 discr-expr)))

(clojure.core/defn- build-invimage-type
  "Build InvImage (· < ·) measure y x as an Expr.
   y and x are Expr (typically bvars)."
  [env alpha-level alpha measure-lam y x]
  (let [nat (e/const' (name/from-string "Nat") [])
        lt-rel (e/lam "x1" nat
                      (e/lam "x2" nat
                             (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                                     nat (e/const' (name/from-string "instLTNat") [])
                                     (e/bvar 1) (e/bvar 0)) :default) :default)]
    (e/app* (e/const' (name/from-string "InvImage") [alpha-level (lvl/succ lvl/zero)])
            alpha nat lt-rel measure-lam y x)))

(clojure.core/defn- discharge-decreasing-proof
  "Build a proof of measure(rec-arg) < measure(current-arg).
   Uses omega to discharge the obligation.
   param-name, param-type: the function parameter (will be universally quantified).
   measure-form: the raw measure expression (in terms of bvar 0 = param).
   rec-arg-form: the argument to the recursive call (in terms of bvar 0 = param).
   Returns a lambda: λ (param : Type) => proof-of-lt."
  [env param-name param-type measure-ansatz rec-arg-ansatz]
  (let [nat (e/const' (name/from-string "Nat") [])
        ;; Build goal: ∀ (param : Type), measure(rec-arg) < measure(param)
        ;; measure-ansatz and rec-arg-ansatz are in terms of bvar 0 = param
        m-rec (e/app (e/lam (str param-name) param-type measure-ansatz :default) rec-arg-ansatz)
        m-cur measure-ansatz ;; measure(param) where param = bvar 0
        lt-goal (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                        nat (e/const' (name/from-string "instLTNat") [])
                        m-rec m-cur)
        ;; Wrap in forall: ∀ (param : Type), lt-goal
        full-goal (e/forall' (str param-name) param-type lt-goal :default)
        ;; Create proof state, intro param, then omega
        [ps _] (proof/start-proof env full-goal)
        ps (basic/intros ps [(str param-name)])
        ps (omega/omega ps)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "Cannot prove termination obligation."
                           "\nGoal: " (e/->string env full-goal))
                      {:goal full-goal})))
    ;; Extract gives us: λ (param) => proof-term
    (extract/extract ps)))

;; ============================================================
;; Guard-aware decrease checking (port of lean4's decreasing-goal generation)
;; ============================================================

(declare prove-theorem)

(clojure.core/defn- wf-subst-syms
  "Replace symbols (and any form that is a key) in `form` per map `m`."
  [form m]
  (cond
    (contains? m form) (get m form)
    (seq? form)        (map #(wf-subst-syms % m) form)
    (vector? form)     (mapv #(wf-subst-syms % m) form)
    :else              form))

(clojure.core/defn- wf-guard-of
  "Map a surface boolean condition + polarity to a Prop guard usable by omega, or nil if the
   condition isn't an arithmetic comparison. Assumes Nat operands (WF measures are Nat).
   (== a b) → (= Nat a b);  (<= a b) → (<= Nat a b);  (< a b) → (< Nat a b);
   (>= a b) → (<= Nat b a);  (> a b) → (< Nat b a).  Negative polarity wraps in (Not …)."
  [cond-form pos?]
  (when (and (seq? cond-form) (= 3 (count cond-form)))
    (let [[op a b] cond-form
          prop (case op
                 == (list '= 'Nat a b)
                 <= (list '<= 'Nat a b)
                 <  (list '< 'Nat a b)
                 >= (list '<= 'Nat b a)
                 >  (list '< 'Nat b a)
                 nil)]
      (when prop (if pos? prop (list 'Not prop))))))

(clojure.core/defn- wf-ctor-pattern
  "Build the `(T.ctor typeargs… fields…)` discriminant pattern for a match branch guard.
   discr-type e.g. Nat or (List Nat); ctor-short e.g. succ; fields e.g. [pred]."
  [discr-type ctor-short fields]
  (let [[thead & targs] (if (seq? discr-type) discr-type [discr-type])
        ctor-full (symbol (str thead "." ctor-short))]
    (if (and (empty? targs) (empty? fields))
      ctor-full
      (cons ctor-full (concat targs fields)))))

(clojure.core/defn- collect-rec-calls-with-guards
  "Walk the surface body, collecting each self-call `(fn-name a0 … a_{n-1})` together with the
   path-condition guards (if/match) and match-bound field binders in scope at that call — the
   ansatz analogue of lean4's recursive-call context (Fix.lean). Returns a vector of
   {:args [arg-forms], :field-binders [[sym type-form] …], :guards [guard-form …]}.
   Match field types currently default to Nat (Stage-1 WF is over Nat measures)."
  [body fn-name n]
  (let [acc (atom [])]
    (letfn [(walk [form guards binders]
              (cond
                (and (seq? form) (= (first form) fn-name) (= n (count (rest form))))
                (swap! acc conj {:args (vec (rest form)) :field-binders binders :guards guards})

                (and (seq? form) (= 'if (first form)))
                (let [[_ c t e] form
                      gt (wf-guard-of c true)
                      ge (wf-guard-of c false)]
                  (walk t (if gt (conj guards gt) guards) binders)
                  (walk e (if ge (conj guards ge) guards) binders))

                (and (seq? form) (= 'match (first form)))
                (let [[_ discr discr-type _result & branches] form]
                  (doseq [br branches]
                    (let [[ctor-short x & more] br
                          [fields bbody] (if (vector? x) [x (first more)] [[] x])
                          field-bs (mapv (fn [f] [f 'Nat]) fields)
                          guard (list '= discr-type discr
                                      (wf-ctor-pattern discr-type ctor-short fields))]
                      (walk bbody (conj guards guard) (into binders field-bs)))))

                (and (seq? form) (= 'let (first form)))
                (let [[_ bnds bbody] form]
                  (doseq [v (take-nth 2 (rest bnds))] (walk v guards binders))
                  (walk bbody guards binders))

                (seq? form)
                (doseq [sub (rest form)] (walk sub guards binders))

                :else nil))]
      (walk body [] [])
      @acc)))

(clojure.core/defn- prove-decrease
  "Discharge one rec-call's decrease obligation:
     ∀ params field-binders, guards → measure[params := args] < measure[params]
   via omega (the goal that lean4's decreasing_tactic produces after `clean_wf`). Returns the
   proved theorem name on success; throws (omega) when the measure does not provably decrease."
  [pairs measure-form {:keys [args field-binders guards]}]
  (let [param-syms (mapv first pairs)
        subst (zipmap param-syms args)
        measure-at-args (wf-subst-syms measure-form subst)
        param-bs  (vec (mapcat (fn [[p t _]] [p :- t]) pairs))
        field-bs  (vec (mapcat (fn [[f t]] [f :- t]) field-binders))
        guard-bs  (vec (mapcat (fn [g i] [(symbol (str "hg" i)) :- g]) guards (range)))
        binders   (vec (concat param-bs field-bs guard-bs))
        goal      (list '< 'Nat measure-at-args measure-form)]
    (prove-theorem (gensym "decr") binders goal '[(omega)])))

(clojure.core/defn- wf-candidate-measures
  "GuessLex default measures restricted to a single Nat measure (lexicographic is Stage 3):
   each Nat parameter, then the sum of all Nat parameters."
  [pairs]
  (let [nat-ps (->> pairs (filter (fn [[_ t _]] (= t 'Nat))) (mapv first))]
    (concat (vec nat-ps)
            (when (> (count nat-ps) 1) [(cons '+ nat-ps)]))))

(clojure.core/defn- wf-guess-measure
  "Synthesize a terminating measure for an unannotated recursive function (lean4's GuessLex,
   restricted to single Nat measures): the first candidate for which EVERY recursive call
   provably decreases (via prove-decrease/omega). Returns the measure form, or nil. Wrong
   guesses fail prove-decrease, so this is sound."
  [pairs body-form fn-name n]
  (let [calls (collect-rec-calls-with-guards body-form fn-name n)]
    (when (seq calls)
      (some (fn [m]
              (when (try (doseq [c calls] (prove-decrease pairs m c)) true
                         (catch Throwable _ false))
                m))
            (wf-candidate-measures pairs)))))

;; ── Stage 1b: lean4-faithful WellFounded.Nat.fix encoding (kernel-ENFORCED termination) ──
;; Port of lean4 mkFix Nat fast path (Fix.lean) + recursive motive refinement
;; (replaceRecApps/MatcherApp.addArg): the match discriminant reaches each decrease proof via the
;; dependent casesOn motive, so the proof is embedded in the term (not a side gate). Single Nat-arg
;; recursion over match/casesOn bodies; non-applicable shapes (if-guards, multi-arg) throw → caller
;; falls back to the (sound) fuel encoding. See memory wf-fix-encoding-mechanism.
(def ^:private wf-fix-counter (atom 9100000))
(defn- wf-fix-fresh [] (swap! wf-fix-counter inc))
(def ^:private wf-fix-NAT (e/const' (name/from-string "Nat") []))

(defn- wf-fix-mk-lt [a b]
  (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero]) wf-fix-NAT
          (e/const' (name/from-string "instLTNat") []) a b))

;; IHType[xref] = (y:dom) → InvImage.{1,1} dom Nat (·<·) measure y xref → Ret
;; dom-ty = the fix's recursion domain (Nat, or Prod Nat Nat when multi-arg packed; both Sort 1).
(defn- wf-fix-ihtype [dom-ty measure-lam ret xref]
  (let [L1 (lvl/succ lvl/zero)
        ltfn (e/lam "n1" wf-fix-NAT (e/lam "n2" wf-fix-NAT (wf-fix-mk-lt (e/bvar 1) (e/bvar 0)) :default) :default)]
    (e/forall' "y" dom-ty
      (e/forall' "_"
        (e/app* (e/const' (name/from-string "InvImage") [L1 L1]) (e/lift dom-ty 1 0) wf-fix-NAT ltfn measure-lam
                (e/bvar 0) (e/lift xref 1 0))
        (e/lift ret 2 0) :default) :default)))

;; mkLambdaFVars: fvs=[[id name type] …] outer→inner; binder k's type may reference earlier ids.
(defn- wf-fix-mk-lambdas [fvs body]
  (let [ids (mapv first fvs) n (count fvs)]
    (loop [k (dec n) acc (e/abstract-many body ids)]
      (if (< k 0) acc
          (let [[_ nm ty] (nth fvs k)]
            (recur (dec k) (e/lam nm (e/abstract-many ty (subvec ids 0 k)) acc :default)))))))

;; telescope a Pi type to fvars, WHNF at each step (minor types are beta-redexes `motive (ctor …)`).
(defn- wf-fix-tele-open [ty reducer]
  (loop [t (.whnf reducer ty) bs []]
    (if (e/forall? t)
      (let [id (wf-fix-fresh)]
        (recur (.whnf reducer (e/instantiate1 (e/forall-body t) (e/fvar id)))
               (conj bs [id (e/forall-name t) (e/forall-type t)])))
      {:binders bs :body t})))

(defn- wf-fix-ty-of [scope id] (some (fn [[i t]] (when (= i id) t)) scope))

;; kernel-native decrease proof: ∀ scope, measure arg < measure P  (P fully pattern-substituted ⇒
;; closed and true), via omega; returned applied to the scope fvars.
(defn- wf-fix-decr-proof [env reducer scope measure-lam arg P]
  (let [ids (mapv first scope) tys (mapv second scope)
        ;; whnfCore the measure application: beta + iota, NO delta (lean4's clean_wf normalizes
        ;; the goal the same way; omega's reifier atomizes unreduced redexes, while full whnf
        ;; would delta-unfold Nat.add into recursors omega cannot read). iota is needed for the
        ;; packed multi-arg measure `Prod.rec … (Prod.mk a b)`. The proof still matches the call
        ;; site's `InvImage … arg P` obligation by defeq.
        m-of (fn [t] (.whnfCore reducer (e/app measure-lam t)))
        prop (wf-fix-mk-lt (m-of arg) (m-of P))
        ;; mkForallFVars: binder i's type may reference earlier scope fvars (e.g. a dite guard
        ;; `h : ¬(x = 0)` mentions x) — abstract each type over ids[0..i), like wf-fix-mk-lambdas.
        gt (loop [i (dec (count ids)) body (e/abstract-many prop ids)]
             (if (< i 0) body
                 (recur (dec i) (e/forall' "s" (e/abstract-many (nth tys i) (subvec ids 0 i)) body :default))))
        [ps _] (proof/start-proof env gt)
        ps (basic/intros ps (mapv #(str "s" %) (range (count ids))))
        ps (reduce run-tactic ps '[(omega)])]
    (when-not (proof/solved? ps)
      (throw (ex-info "wf-fix: decrease not provable" {:goal (e/->string gt)})))
    (extract/verify ps)
    (apply e/app* (extract/extract ps) (mapv e/fvar ids))))

;; The Prod.Lex layer (Prod.Lex, Prod.lex, lexAccessible, Lex.right') panics through the standard
;; init export path only because of unrelated wfParam machinery — exported standalone it is clean,
;; bundled as resources/ansatz/lex-prelude.ndjson.gz. Loaded lazily (idempotent) when a
;; lexicographic :termination-by is first used: each missing declaration is kernel-VERIFIED on
;; admission (verify? true); declarations already in the env are skipped (the export carries its
;; full dependency closure).
(clojure.core/defn wf-fix-ensure-lex-prelude!
  "Ensure the Prod.Lex prelude is loaded into the global env (idempotent)."
  []
  (when-not (env/lookup @ansatz-env (name/from-string "Prod.Lex.right'"))
    (let [res (clojure.java.io/resource "ansatz/lex-prelude.ndjson.gz")
          _ (when-not res (throw (ex-info "lex prelude not on classpath (resources/ansatz/lex-prelude.ndjson.gz)" {})))
          ndjson (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))] (slurp in))
          decls (:decls (parser/parse-ndjson-string ndjson))
          env'
          (loop [ds (seq decls) env @ansatz-env]
            (if-let [ci (first ds)]
              (cond
                (env/lookup env (.name ^ansatz.kernel.ConstantInfo ci))
                (recur (next ds) env)
                (.isInduct ^ansatz.kernel.ConstantInfo ci)
                (let [{:keys [members rest]} (replay/collect-inductive-bundle ds)
                      [env2 rs] (replay/replay-inductive-bundle env members)]
                  (when-let [err (first (filter #(= :error (:status %)) rs))]
                    (throw (ex-info (str "lex prelude replay failed: " (:name err) " — " (:error err)) {})))
                  (recur rest env2))
                :else
                (let [[env2 r] (replay/replay-one env ci true)]
                  (when (= :error (:status r))
                    (throw (ex-info (str "lex prelude replay failed: " (:name r) " — " (:error r)) {})))
                  (recur (next ds) env2)))
              env))]
      (reset! ansatz-env env')
      (when *verbose* (println "  ✓ Prod.Lex prelude loaded (kernel-verified)")))))

;; one omega-proved arithmetic fact, ∀-closed over scope and applied back to the scope fvars
(defn- wf-fix-omega-fact [env scope prop]
  (let [ids (mapv first scope) tys (mapv second scope)
        gt (loop [i (dec (count ids)) body (e/abstract-many prop ids)]
             (if (< i 0) body
                 (recur (dec i) (e/forall' "s" (e/abstract-many (nth tys i) (subvec ids 0 i)) body :default))))
        [ps _] (proof/start-proof env gt)
        ps (basic/intros ps (mapv #(str "s" %) (range (count ids))))
        ps (run-tactic ps '(omega))]
    (when-not (proof/solved? ps)
      (throw (ex-info "wf-fix: omega fact not provable" {:goal (e/->string gt)})))
    (extract/verify ps)
    (apply e/app* (extract/extract ps) (mapv e/fvar ids))))

;; lexicographic decrease proof (lean4 decreasing_tactic peel, WFTactics.lean:59), constructed
;; DIRECTLY: `Prod.Lex.left` when the first measure strictly drops, else `Prod.Lex.right'` (the
;; <=-variant of Lex.right, WF.lean:324 — subsumes the equal-first-component case). The omega base
;; facts are stated in the LT.lt/LE.le instance spelling (what omega certifies); the constructors
;; expect Nat.lt — defeq (instLTNat unfolds to Nat.lt), check-constant arbitrates.
(defn- wf-fix-decr-proof-lex2 [env reducer scope tup-lam arg P]
  (let [t-of (fn [t] (.whnfCore reducer (e/app tup-lam t)))
        natlt (e/const' (name/from-string "Nat.lt") [])
        nat-le (fn [a b] (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) wf-fix-NAT
                                 (e/const' (name/from-string "instLENat") []) a b))
        tup-arg (t-of arg) tup-P (t-of P)
        unmk (fn [t] (let [[h as] (e/get-app-fn-args t)]
                       (when (and (e/const? h) (= "Prod.mk" (name/->string (e/const-name h)))
                                  (= 4 (count as)))
                         [(nth as 2) (nth as 3)])))
        [A1 A2] (or (unmk tup-arg) (throw (ex-info "wf-fix: lex measure tuple did not reduce" {})))
        [P1 P2] (or (unmk tup-P) (throw (ex-info "wf-fix: lex measure tuple did not reduce" {})))]
    (try
      ;; first component strictly decreases
      (let [h (wf-fix-omega-fact env scope (wf-fix-mk-lt A1 P1))]
        (e/app* (e/const' (name/from-string "Prod.Lex.left") [lvl/zero lvl/zero])
                wf-fix-NAT wf-fix-NAT natlt natlt A1 A2 P1 P2 h))
      (catch Exception _
        ;; first non-increasing, second strictly decreases
        (let [h1 (wf-fix-omega-fact env scope (nat-le A1 P1))
              h2 (wf-fix-omega-fact env scope (wf-fix-mk-lt A2 P2))]
          (e/app* (e/const' (name/from-string "Prod.Lex.right'") [lvl/zero])
                  wf-fix-NAT natlt P1 P2 A1 A2 h1 h2))))))

;; is this app a recursor whose major is a free fvar occurring in P? → refinable.
(defn- wf-fix-refinable? [env h as P]
  (and (e/const? h)
       (.endsWith (name/->string (e/const-name h)) ".rec")
       (env/lookup env (e/const-name h))
       (let [rci (env/lookup env (e/const-name h))]
         (and (= (count as) (+ (.numParams rci) 1 (.numMinors rci) (.numIndices rci) 1))
              (e/fvar? (last as))
              (let [vid (e/fvar-id (last as))
                    fvids (atom #{})]
                ((fn go [x] (cond (e/fvar? x) (swap! fvids conj (e/fvar-id x))
                                  (e/app? x) (do (go (e/app-fn x)) (go (e/app-arg x)))
                                  (e/lam? x) (do (go (e/lam-type x)) (go (e/lam-body x)))
                                  (e/forall? x) (do (go (e/forall-type x)) (go (e/forall-body x)))
                                  :else nil)) P)
                (contains? @fvids vid))))))

(declare wf-fix-refine)

;; refine recursor (R.rec params motive minors… major) to thread ih-fvar, exposing each branch's
;; pattern via the dependent motive. Returns the refined recursor APPLIED to ih-fvar.
(defn- wf-fix-refine-rec [env callspec ret reducer rec-head call-args ih-fvar P scope]
  (let [rv (first (e/const-levels rec-head)) rec-name (e/const-name rec-head)
        rci (env/lookup env rec-name) np (.numParams rci) nminors (.numMinors rci)
        params (vec (take np call-args))
        major (last call-args) v-id (e/fvar-id major)
        T (wf-fix-ty-of scope v-id)
        tc (ansatz.kernel.TypeChecker. env) _ (.setFuel tc (long config/*default-fuel*))
        ind-name (let [s (name/->string rec-name)] (name/from-string (subs s 0 (- (count s) 4))))
        ctor-names (vec (.ctors (env/lookup env ind-name)))
        P-abs (e/abstract-many P [v-id])
        inner-motive (e/lam "v" T (e/forall' "_" ((:ihtype callspec) P-abs) (e/lift ret 1 0) :default) :default)
        rec-applied (apply e/app* (e/const' rec-name (vec (e/const-levels rec-head))) (conj params inner-motive))
        tb (:binders (wf-fix-tele-open (.inferType tc rec-applied) reducer))
        minor-types (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) tb) i)) (range nminors))
        process (fn [mi]
                  (let [ctor-name (nth ctor-names mi) nf (.numFields (env/lookup env ctor-name))
                        bs (:binders (wf-fix-tele-open (nth minor-types mi) reducer)) bid (mapv first bs)
                        field-ids (vec (take nf bid))
                        field-tys (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) bs) i)) (range nf))
                        fs-id (last bid)
                        ctor-pat (apply e/app* (e/const' ctor-name (vec (rest (e/const-levels rec-head))))
                                        (into params (mapv e/fvar field-ids)))
                        Pc (e/instantiate1 (e/abstract-many P [v-id]) ctor-pat)
                        scope2 (into scope (mapv vector field-ids field-tys))
                        orig (nth call-args (+ np 1 mi)) nopen (dec (count bs))
                        obody (loop [b orig i 0] (if (and (< i nopen) (e/lam? b))
                                                   (recur (e/instantiate1 (e/lam-body b) (e/fvar (nth bid i))) (inc i)) b))
                        refined (wf-fix-refine env callspec ret reducer obody (e/fvar fs-id) Pc scope2)]
                    (wf-fix-mk-lambdas bs refined)))
        minors' (mapv process (range nminors))
        refined-rec (apply e/app* (e/const' rec-name (vec (e/const-levels rec-head))) (-> (into params [inner-motive]) (into minors') (conj major)))]
    (e/app refined-rec ih-fvar)))

;; descend a branch body: rewrite self-calls to (ih arg proof), refine nested recursors, open lambdas.
;; Bool comparison head → [Prop, Decidable instance] builders (the same comparison→Prop mapping as
;; Stage 1a's wf-guard-of, but term-level). Props match the instances' indices exactly
;; (Nat.decEq : Decidable (Eq Nat a b), Nat.decLt : Decidable (LT.lt Nat instLTNat a b), …).
(def ^:private wf-fix-comparisons
  {"Nat.beq" (fn [a b] [(e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) wf-fix-NAT a b)
                        (e/app* (e/const' (name/from-string "Nat.decEq") []) a b)])
   "Nat.blt" (fn [a b] [(wf-fix-mk-lt a b)
                        (e/app* (e/const' (name/from-string "Nat.decLt") []) a b)])
   "Nat.ble" (fn [a b] [(e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) wf-fix-NAT
                                (e/const' (name/from-string "instLENat") []) a b)
                        (e/app* (e/const' (name/from-string "Nat.decLe") []) a b)])})

;; our if-compile: Bool.rec M else-br then-br (cmp a b), with a CONSTANT motive
(defn- wf-fix-ite? [h as]
  (and (e/const? h)
       (= "Bool.rec" (name/->string (e/const-name h)))
       (= 4 (count as))
       (let [M (nth as 0) [ch cas] (e/get-app-fn-args (nth as 3))]
         (and (e/lam? M) (not (e/has-loose-bvars? (e/lam-body M)))
              (e/const? ch)
              (contains? wf-fix-comparisons (name/->string (e/const-name ch)))
              (= 2 (count cas))))))

;; lean4-faithful if-guard: in lean4, ite/dite are @[macro_inline], so the WF translation sees
;; `Decidable.casesOn inst (fun h:¬c => else) (fun h:c => then)` — the guard is a constructor FIELD
;; of Decidable, exposed by the same casesOn mechanism as match patterns (Fix.lean has NO ite case).
;; Our surface compiles `if` to Bool.rec over a Bool comparison, which loses the guard; convert it
;; here to `dite P inst (fun h:P => then') (fun h:¬P => else')` so each branch binds the hypothesis
;; the decrease proof needs (e.g. `¬(x = 0) → x - 1 < x`). No motive refinement is needed: unlike
;; match, the IH type does not change between if-branches — only a hypothesis is added to scope.
(defn- wf-fix-ite->dite [env callspec ret reducer rec-head as ih-fvar P scope]
  (let [rv (first (e/const-levels rec-head))
        M (nth as 0) else-br (nth as 1) then-br (nth as 2)
        [ch cas] (e/get-app-fn-args (nth as 3))
        ;; condition operands may themselves contain rec-calls — refine first, build P from refined
        a (wf-fix-refine env callspec ret reducer (nth cas 0) ih-fvar P scope)
        b (wf-fix-refine env callspec ret reducer (nth cas 1) ih-fvar P scope)
        [prop inst] ((wf-fix-comparisons (name/->string (e/const-name ch))) a b)
        ;; constant motive: extract the codomain (instantiate the unused Bool binder away)
        ret-here (e/instantiate1 (e/lam-body M) (e/const' (name/from-string "Bool.true") []))
        not-prop (e/app (e/const' (name/from-string "Not") []) prop)
        ht (wf-fix-fresh) he (wf-fix-fresh)
        then' (wf-fix-refine env callspec ret reducer then-br ih-fvar P (conj scope [ht prop]))
        else' (wf-fix-refine env callspec ret reducer else-br ih-fvar P (conj scope [he not-prop]))]
    (e/app* (e/const' (name/from-string "dite") [rv])
            ret-here prop inst
            (wf-fix-mk-lambdas [[ht "h" prop]] then')
            (wf-fix-mk-lambdas [[he "h" not-prop]] else'))))

;; callspec: {:cname Name, :arity n, :pack (fn [refined-args] packed-arg)} — for multi-arg
;; functions the recursion args are packed (Prod.mk) into the single fix argument.
(defn- wf-fix-refine [env callspec ret reducer body ih-fvar P scope]
  (let [[h as] (e/get-app-fn-args body)]
    (cond
      (and (e/const? h) (= (e/const-name h) (:cname callspec)) (= (:arity callspec) (count as)))
      (let [args' (mapv #(wf-fix-refine env callspec ret reducer % ih-fvar P scope) as)
            arg ((:pack callspec) args')]
        (e/app* ih-fvar arg ((:decr callspec) env reducer scope arg P)))
      (wf-fix-refinable? env h as P)
      (wf-fix-refine-rec env callspec ret reducer h as ih-fvar P scope)
      (wf-fix-ite? h as)
      (wf-fix-ite->dite env callspec ret reducer h as ih-fvar P scope)
      (seq as)
      (apply e/app* (wf-fix-refine env callspec ret reducer h ih-fvar P scope)
             (mapv #(wf-fix-refine env callspec ret reducer % ih-fvar P scope) as))
      (e/lam? body)
      (let [id (wf-fix-fresh) bt (e/lam-type body)
            inner (wf-fix-refine env callspec ret reducer
                                 (e/instantiate1 (e/lam-body body) (e/fvar id)) ih-fvar P (conj scope [id bt]))]
        (e/lam (e/lam-name body) bt (e/abstract-many inner [id]) (e/lam-info body)))
      :else body)))

;; ── Stage 1b-D: defining equations for wf-fix functions (lean4 WF/Unfold.lean rwFixEq) ──
;; A wf-fix definition does NOT unfold definitionally on a symbolic argument (WellFounded.fix is
;; stuck on the Acc proof), so simp needs explicit equations. Per lean4: one WellFounded.Nat.fix_eq
;; instance proves `f x = Ffn x (fun y _ => f y)`; we state per-LEAF equations (fully-composed
;; constructor patterns, e.g. `f (succ (succ k)) = succ (f k)`) so every discriminant in the
;; refined casesOn is constructor-headed and the stated RHS is defeq to fix_eq's RHS by iota/beta
;; alone (the decrease proofs are beta-dropped by `fun y _ => f y`). The bare fix_eq instance IS
;; the proof; check-constant carries the defeq burden. Leaf splitting is REQUIRED, not cosmetic:
;; a still-symbolic nested match is stuck with a refined motive on one side and the original on
;; the other — not defeq (this is why lean4 has eq_N splitting / the matcher arg_pusher).

;; rhs converter: same dite conversion as wf-fix-ite->dite but recursive calls stay as the
;; function constant (no IH threading) — produces the equation's right-hand side.
(defn- wf-fix-eq-rhs [env body]
  (let [[h as] (e/get-app-fn-args body)]
    (cond
      (wf-fix-ite? h as)
      (let [rv (first (e/const-levels h))
            M (nth as 0) else-br (nth as 1) then-br (nth as 2)
            [ch cas] (e/get-app-fn-args (nth as 3))
            a (wf-fix-eq-rhs env (nth cas 0)) b (wf-fix-eq-rhs env (nth cas 1))
            [prop inst] ((wf-fix-comparisons (name/->string (e/const-name ch))) a b)
            ret-here (e/instantiate1 (e/lam-body M) (e/const' (name/from-string "Bool.true") []))
            not-prop (e/app (e/const' (name/from-string "Not") []) prop)]
        (e/app* (e/const' (name/from-string "dite") [rv]) ret-here prop inst
                (e/lam "h" prop (e/lift (wf-fix-eq-rhs env then-br) 1 0) :default)
                (e/lam "h" not-prop (e/lift (wf-fix-eq-rhs env else-br) 1 0) :default)))
      (seq as) (apply e/app* (wf-fix-eq-rhs env h) (mapv #(wf-fix-eq-rhs env %) as))
      (e/lam? body) (e/lam (e/lam-name body) (wf-fix-eq-rhs env (e/lam-type body))
                           (wf-fix-eq-rhs env (e/lam-body body)) (e/lam-info body))
      :else body)))

;; leaf enumerator: split each case-split-on-a-pattern-var per constructor, composing the
;; pattern; stop at dites/leaves. fields = the ∀-binders of the equation ([[id type] …]);
;; a split consumes the matched var and appends the constructor's fields.
(defn- wf-fix-eq-leaves [env tc reducer body pattern fields]
  (let [[h as] (e/get-app-fn-args body)]
    (if (wf-fix-refinable? env h as pattern)
      (let [rec-name (e/const-name h)
            rci (env/lookup env rec-name) np (.numParams rci) nminors (.numMinors rci)
            params (vec (take np as))
            major (last as) v-id (e/fvar-id major)
            ind-name (let [s (name/->string rec-name)] (name/from-string (subs s 0 (- (count s) 4))))
            ctor-names (vec (.ctors (env/lookup env ind-name)))
            rec-applied (apply e/app* (e/const' rec-name (vec (e/const-levels h))) (conj params (nth as np)))
            tb (:binders (wf-fix-tele-open (.inferType tc rec-applied) reducer))
            minor-types (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) tb) i)) (range nminors))]
        (vec (mapcat
              (fn [mi]
                (let [ctor-name (nth ctor-names mi) nf (.numFields (env/lookup env ctor-name))
                      bs (:binders (wf-fix-tele-open (nth minor-types mi) reducer)) bid (mapv first bs)
                      field-ids (vec (take nf bid))
                      field-tys (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) bs) i)) (range nf))
                      ctor-pat (apply e/app* (e/const' ctor-name (vec (rest (e/const-levels h))))
                                      (into params (mapv e/fvar field-ids)))
                      pattern' (e/instantiate1 (e/abstract-many pattern [v-id]) ctor-pat)
                      fields' (into (vec (remove (fn [[id _]] (= id v-id)) fields))
                                    (mapv vector field-ids field-tys))
                      ;; open the ORIGINAL minor: nf fields + structural-ih binders (unused in
                      ;; WF bodies — recursive calls reference the function constant)
                      orig (nth as (+ np 1 mi))
                      obody (loop [b orig i 0] (if (and (< i (count bs)) (e/lam? b))
                                                 (recur (e/instantiate1 (e/lam-body b) (e/fvar (nth bid i))) (inc i)) b))]
                  (wf-fix-eq-leaves env tc reducer obody pattern' fields')))
              (range nminors))))
      [{:fields fields :pattern pattern :rhs (wf-fix-eq-rhs env body)}])))

;; Build the (unapplied) fix term: param-type → ret. raw-body = the compiled body with the
;; (possibly packed) recursion param at bvar 0 (any shape: match/casesOn, if/Bool.rec, or mixed —
;; the general refine dispatcher routes each; for multi-arg the caller wraps the body in Prod.rec
;; and the callspec packs recursive-call args). The callspec carries the relation specifics:
;;   :ihtype  (fn [xref] IHType[xref])  — the IH function type over the recursion domain
;;   :decr    (fn [env reducer scope arg P] proof) — one decrease proof
;;   :fix     (fn [ret-level Ffn] fix-term) — wraps the refined functional in the fix combinator
;;            (WellFounded.Nat.fix for a single Nat measure, WellFounded.fix for lexicographic)
;; Throws if a decrease obligation is unprovable.
(defn- wf-fix-encode [env callspec raw-body ret param-type]
  (let [tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel (long config/*default-fuel*)))
        reducer (.getReducer tc)
        ret-sort (.inferType tc ret)
        ret-level (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))
        Xid (wf-fix-fresh) Fvid (wf-fix-fresh) X (e/fvar Xid)
        Fty ((:ihtype callspec) X) Fv (e/fvar Fvid)
        rawX (e/instantiate1 raw-body X)
        body' (wf-fix-refine env callspec ret reducer rawX Fv X [[Xid param-type]])
        Ffn (wf-fix-mk-lambdas [[Xid "x" param-type] [Fvid "F" Fty]] body')]
    ((:fix callspec) ret-level Ffn)))

(declare build-telescope-fvar)
(clojure.core/defn define-verified-wf
  "Define a verified function with well-founded recursion.
   Uses WellFounded.Nat.fix from the environment.
   Returns compiled Clojure fn."
  [fn-name params ret-type-form body-form measure-form]
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)

        ;; Guard-aware termination check (lean4's decreasing goals; replaces fuel-trust): every
        ;; recursive call must provably decrease the measure under its path-condition guards.
        ;; The fuel encoding below is total either way; this gate is what makes :termination-by an
        ;; honest proof — a non-terminating definition (measure that doesn't decrease) is rejected.
        ;; A lexicographic (vector) measure skips this scalar gate: its only encoding is the
        ;; WellFounded.fix term below, whose embedded Prod.Lex proofs ARE the termination check.
        _ (when-not (vector? measure-form)
            (doseq [c (collect-rec-calls-with-guards body-form fn-name n)]
              (try (prove-decrease pairs measure-form c)
                   (catch Throwable e
                     (throw (ex-info (str "Cannot prove `" fn-name "` terminates: measure `"
                                          measure-form "` is not provably decreasing on the recursive "
                                          "call with args " (:args c)
                                          (when (seq (:guards c)) (str " under guards " (:guards c)))
                                          ". Adjust :termination-by, or use ^:partial.")
                                     {:fn fn-name :kind :termination-decrease-failed :call c}))))))

        ;; Build the function type: ∀ params → ret-type (same as define-verified)
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
        ret-ansatz (sexp->ansatz env scope-full n ret-type-form)
        type-ansatz (loop [i (dec n) body ret-ansatz]
                      (if (< i 0) body
                          (let [[pn pt binfo] (nth pairs i)
                                s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                                ty (sexp->ansatz env s i pt)]
                            (recur (dec i) (e/forall' (str pn) ty body binfo)))))

        ;; Compile param types
        param-types (mapv (fn [[_ pt-form]]
                            (sexp->ansatz env {} 0 pt-form))
                          pairs)
        cname (name/from-string (str fn-name))

        ;; Fork env and add temporary axiom for self-reference
        tmp-ci (env/mk-axiom cname [] type-ansatz)
        tmp-env (env/add-constant (env/fork env) tmp-ci)

        ;; Compile body fvar-first (consistent with define-verified) on the forked env —
        ;; self-calls resolve to the axiom const; replace-rec-calls rewrites them to the IH below.
        body-ansatz (binding [surface-match/*use-cases-on?* true]
                      (build-telescope-fvar tmp-env pairs ret-type-form body-form))

        ;; Peel all outer lambdas to get the raw body
        raw-body (loop [e body-ansatz i 0]
                   (if (and (< i n) (e/lam? e))
                     (recur (e/lam-body e) (inc i))
                     e))

        ;; Compile measure expression — uses all params in scope
        ;; Bind *scope-types* so auto-elaborate can infer implicit args from param types
        ;; A vector measure form is a LEXICOGRAPHIC tuple: compile each component; the scalar
        ;; measure-ansatz is then only fuel-path scaffolding (unused — lex never takes fuel).
        nat (e/const' (name/from-string "Nat") [])
        scope-types-map (into {} (map (fn [[p _ _] pt] [p pt]) pairs param-types))
        lex-measures (when (vector? measure-form)
                       (binding [*scope-types* scope-types-map]
                         (mapv #(sexp->ansatz env scope-full n %) measure-form)))
        measure-ansatz (binding [*scope-types* scope-types-map]
                         (sexp->ansatz env scope-full n
                                       (if (vector? measure-form) (first measure-form) measure-form)))

        ;; Universe level for return type
        tc-tmp (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc-tmp (long config/*default-fuel*))
        ret-sort (.inferType tc-tmp ret-ansatz)
        ret-level (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))

        ;; Fuel-based approach: Nat.rec on fuel (matching Lean 4's kernel-level pattern).
        ;; For n params: step = λ fuel ih p1 p2 ... pn => body[fn(a1..an) → ih(a1..an)]
        ;; raw-body has params at bvar 0..n-1 (p1=bvar 0, p2=bvar 1, etc.)
        ;; In the step body: pn=bvar 0, ..., p1=bvar n-1, ih=bvar n, fuel=bvar n+1
        ;; Since raw-body's bvar layout matches the step's param layout, no lifting needed.
        ;; ih is at depth n relative to the step body.
        replaced-body (replace-rec-calls raw-body cname n n nil)

        ;; Build multi-arg arrow type: p1 → p2 → ... → ret
        arrow-type (loop [i (dec n) ty ret-ansatz]
                     (if (< i 0) ty
                         (recur (dec i)
                                (e/forall' (str (first (nth pairs i)))
                                           (nth param-types i) ty :default))))

        ;; Build Nat.rec components
        nat-rec (e/const' (name/from-string "Nat.rec") [ret-level])
        motive-nr (e/lam "fuel" nat arrow-type :default)
        ;; base: λ p1 p2 ... pn => default (unreachable with correct fuel)
        ;; Use type-appropriate default value
        default-val (let [[rh ra] (e/get-app-fn-args ret-ansatz)]
                      (cond
                        ;; Nat → 0
                        (and (e/const? ret-ansatz)
                             (= "Nat" (name/->string (e/const-name ret-ansatz))))
                        (e/lit-nat 0)
                        ;; List α → List.nil α
                        (and (e/const? rh)
                             (= "List" (name/->string (e/const-name rh))))
                        (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                               (first ra))
                        ;; Bool → false
                        (and (e/const? ret-ansatz)
                             (= "Bool" (name/->string (e/const-name ret-ansatz))))
                        (e/const' (name/from-string "Bool.false") [])
                        ;; Fallback: try Inhabited.default
                        :else
                        (let [inh-inst (try-synthesize-instance
                                        env (e/app (e/const' (name/from-string "Inhabited") [(lvl/succ lvl/zero)])
                                                   ret-ansatz))]
                          (if inh-inst
                            (e/app* (e/const' (name/from-string "Inhabited.default") [(lvl/succ lvl/zero)])
                                    ret-ansatz inh-inst)
                            ;; Last resort: use lit-nat 0 (may cause type error if reached)
                            (e/lit-nat 0)))))
        base-nr (loop [i (dec n) body default-val]
                  (if (< i 0) body
                      (recur (dec i)
                             (e/lam (str (first (nth pairs i)))
                                    (nth param-types i) body :default))))
        ;; step: λ fuel ih p1 p2 ... pn => replaced-body
        step-nr (e/lam "fuel" nat
                       (e/lam "ih" arrow-type
                              (loop [i (dec n) body replaced-body]
                                (if (< i 0) body
                                    (recur (dec i)
                                           (e/lam (str (first (nth pairs i)))
                                                  (nth param-types i) body :default))))
                              :default) :default)
        ;; fuel = Nat.succ (measure(params)) where params are bvar 0..n-1 in the outer lambda
        fuel-expr (e/app (e/const' (name/from-string "Nat.succ") []) measure-ansatz)
        ;; Full: λ p1 ... pn => (Nat.rec motive base step fuel) p1 ... pn
        ;; Build inner: apply Nat.rec result to all params
        inner-app (reduce (fn [f i] (e/app f (e/bvar (- n 1 i))))
                          (e/app* nat-rec motive-nr base-nr step-nr fuel-expr)
                          (range n))
        ;; Wrap in outer lambdas
        final-body (loop [i (dec n) body inner-app]
                     (if (< i 0) body
                         (recur (dec i)
                                (e/lam (str (first (nth pairs i)))
                                       (nth param-types i) body :default))))

        ;; Stage 1b: prefer the lean4-faithful WellFounded.Nat.fix encoding (kernel-ENFORCED
        ;; termination — the decrease proof lives in the term). Single Nat arg directly; two Nat
        ;; args via Prod packing (lean4 packs through PSigma.casesOn, Fix.lean:183 — the packing
        ;; wrapper is just another refinable recursor for our refine-rec). Bodies may be
        ;; match/casesOn, if/Bool.rec (converted to dite, exposing the guard like lean4's
        ;; macro_inline ite), or mixed. On any unsupported shape or check failure, fall back to
        ;; the (sound, gate-checked) fuel encoding above.
        all-nat? (every? (fn [pt] (and (e/const? pt) (= "Nat" (name/->string (e/const-name pt)))))
                         param-types)
        nat-c (e/const' (name/from-string "Nat") [])
        L0 lvl/zero
        L1 (lvl/succ lvl/zero)
        ;; relation spec for a single Nat measure → WellFounded.Nat.fix
        mk-measure-relspec
        (fn [dom-ty m-lam]
          {:ihtype (fn [xref] (wf-fix-ihtype dom-ty m-lam ret-ansatz xref))
           :decr (fn [env2 reducer scope arg P] (wf-fix-decr-proof env2 reducer scope m-lam arg P))
           :fix (fn [ret-level Ffn]
                  (apply e/app* (e/const' (name/from-string "WellFounded.Nat.fix") [L1 ret-level])
                         [dom-ty (e/lam "x" dom-ty (e/lift ret-ansatz 1 0) :default) m-lam Ffn]))})
        ;; relation spec for a lexicographic 2-tuple of Nat measures → general WellFounded.fix
        ;; with rel = fun y x => Prod.Lex Nat.lt Nat.lt (tup y) (tup x) and the wf proof projected
        ;; from invImage tup (Prod.lex Nat.lt_wfRel Nat.lt_wfRel) — defeq to the stated relation
        ;; (lean4 Rel.lean:57 builds exactly this invImage; we state the relation beta-expanded
        ;; so each call-site obligation whnfs to a bare Prod.Lex goal).
        mk-lex2-relspec
        (fn [dom-ty tup-lam]
          (let [natlt (e/const' (name/from-string "Nat.lt") [])
                p2-ty (e/app* (e/const' (name/from-string "Prod") [L0 L0]) nat-c nat-c)
                lexr (fn [a b] (e/app* (e/const' (name/from-string "Prod.Lex") [L0 L0]) nat-c nat-c
                                       natlt natlt a b))
                rel-lam (e/lam "y" dom-ty
                          (e/lam "x" (e/lift dom-ty 1 0)
                            (lexr (e/app tup-lam (e/bvar 1)) (e/app tup-lam (e/bvar 0))) :default) :default)
                wfRel (e/app* (e/const' (name/from-string "invImage") [L1 L1]) dom-ty p2-ty tup-lam
                              (e/app* (e/const' (name/from-string "Prod.lex") [L0 L0]) nat-c nat-c
                                      (e/const' (name/from-string "Nat.lt_wfRel") [])
                                      (e/const' (name/from-string "Nat.lt_wfRel") [])))
                hwf (e/proj (name/from-string "WellFoundedRelation") 1 wfRel)]
            {:ihtype (fn [xref]
                       (e/forall' "y" dom-ty
                         (e/forall' "_"
                           (lexr (e/app tup-lam (e/bvar 0)) (e/app tup-lam (e/lift xref 1 0)))
                           (e/lift ret-ansatz 2 0) :default) :default))
             :decr (fn [env2 reducer scope arg P] (wf-fix-decr-proof-lex2 env2 reducer scope tup-lam arg P))
             :fix (fn [ret-level Ffn]
                    (apply e/app* (e/const' (name/from-string "WellFounded.fix") [L1 ret-level])
                           [dom-ty (e/lam "x" dom-ty (e/lift ret-ansatz 1 0) :default) rel-lam hwf Ffn]))}))
        lex? (vector? measure-form)
        fix-info
        (cond
          (and (= n 1) all-nat? (not lex?))
          (try
            (let [m-lam (e/lam (str (first (nth pairs 0))) (nth param-types 0) measure-ansatz :default)
                  callspec (merge {:cname cname :arity 1 :pack first :dom (nth param-types 0)}
                                  (mk-measure-relspec (nth param-types 0) m-lam))
                  t (wf-fix-encode env callspec raw-body ret-ansatz (nth param-types 0))]
              (env/check-constant env (env/mk-def cname [] type-ansatz t))
              {:value t :fix t :eqbody raw-body :packed-ty (nth param-types 0) :arity 1})
            (catch Throwable t
              (when *verbose*
                (println (str "  wf-fix encoding unavailable for " fn-name " ("
                              (.getMessage t) ") — using fuel encoding")))
              nil))

          (and (= n 2) all-nat?)
          (try
            (let [packed-ty (e/app* (e/const' (name/from-string "Prod") [L0 L0]) nat-c nat-c)
                  tc0 (doto (ansatz.kernel.TypeChecker. env) (.setFuel (long config/*default-fuel*)))
                  rs (.inferType tc0 ret-ansatz)
                  rv (if (e/sort? rs) (e/sort-level rs) L1)
                  ;; wrap the 2-param body (x=bvar 1, y=bvar 0) in Prod.rec over the packed param
                  ;; (bvar 0 of the wrapper) — the minor's two binders restore the bvar layout.
                  wrap2 (fn [body-2 motive-cod cod-lvl]
                          (e/app* (e/const' (name/from-string "Prod.rec") [cod-lvl L0 L0]) nat-c nat-c
                                  (e/lam "_p" packed-ty (e/lift motive-cod 1 0) :default)
                                  (e/lam (str (first (nth pairs 0))) nat-c
                                         (e/lam (str (first (nth pairs 1))) nat-c body-2 :default) :default)
                                  (e/bvar 0)))
                  wrapped (wrap2 raw-body ret-ansatz rv)
                  pack (fn [args] (e/app* (e/const' (name/from-string "Prod.mk") [L0 L0]) nat-c nat-c
                                          (nth args 0) (nth args 1)))
                  relspec (if lex?
                            (let [_ (wf-fix-ensure-lex-prelude!)
                                  p2-ty (e/app* (e/const' (name/from-string "Prod") [L0 L0]) nat-c nat-c)
                                  tup-body (e/app* (e/const' (name/from-string "Prod.mk") [L0 L0]) nat-c nat-c
                                                   (nth lex-measures 0) (nth lex-measures 1))
                                  tup-lam (e/lam "p" packed-ty (wrap2 tup-body p2-ty L1) :default)]
                              (mk-lex2-relspec packed-ty tup-lam))
                            (mk-measure-relspec packed-ty
                                                (e/lam "p" packed-ty (wrap2 measure-ansatz nat-c L1) :default)))
                  ;; the prelude may have extended the global env — encode against the latest
                  env-l (if lex? @ansatz-env env)
                  callspec (merge {:cname cname :arity 2 :pack pack :dom packed-ty} relspec)
                  fix-t (wf-fix-encode env-l callspec wrapped ret-ansatz packed-ty)
                  ;; user-facing 2-arg value: fun x y => fix (Prod.mk x y)  (fix-t is closed)
                  v (e/lam (str (first (nth pairs 0))) nat-c
                           (e/lam (str (first (nth pairs 1))) nat-c
                                  (e/app fix-t (pack [(e/bvar 1) (e/bvar 0)])) :default) :default)]
              (env/check-constant env-l (env/mk-def cname [] type-ansatz v))
              {:value v :fix fix-t :eqbody wrapped :packed-ty packed-ty :arity 2})
            (catch Throwable t
              (when *verbose*
                (println (str "  wf-fix encoding unavailable for " fn-name " ("
                              (.getMessage t) ") — using fuel encoding")))
              nil)))
        ;; a lexicographic measure has NO single-Nat fuel — the fuel fallback cannot encode it
        _ (when (and lex? (nil? fix-info))
            (throw (ex-info (str "Cannot prove `" fn-name "` terminates: lexicographic measure `"
                                 measure-form "` did not yield a verified WellFounded.fix encoding "
                                 "(each recursive call must decrease the tuple lexicographically).")
                            {:fn fn-name :kind :termination-lex-failed})))
        encoding (if fix-info :wf-fix :fuel)
        chosen-body (or (:value fix-info) final-body)

        ;; Type-check on the real env
        tc (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc (long config/*default-fuel*))
        _ (.inferType tc chosen-body)

        ;; Add to environment (swap! to avoid stale env race)
        ci (env/mk-def cname [] type-ansatz chosen-body)
        _ (swap! ansatz-env env/check-constant ci)
        ;; Register arity for Clojure compilation (FAP/PAP dispatch)
        _ (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
        _ (when *verbose* (println (str "✓ " fn-name " defined (well-founded recursion, "
                                        (case encoding
                                          :wf-fix (if lex? "kernel-enforced lexicographic WellFounded.fix"
                                                      "kernel-enforced WellFounded.Nat.fix")
                                          "fuel + termination gate") ")")))

        ;; Generate equation theorem: fn(args) = body[fn → fn]
        ;; For the fuel-based Nat.rec approach, this is true by computation:
        ;; Nat.rec motive base step (succ k) args = step k (Nat.rec ... k) args
        ;; which is = body[ih → fn] (the original body with recursive calls intact).
        ;; The proof is just Eq.refl (fn args).
        ;; For the wf-fix encoding, whnf of fn(args) is STUCK on the Acc proof, so the equations
        ;; come from WellFounded.Nat.fix_eq instead: per-leaf `<fn>.eq_N` theorems (the names simp's
        ;; find-eqn-theorems discovers), each proven by the bare fix_eq instance + kernel defeq.
        _ (if (= encoding :wf-fix)
            (try
              (let [env' @ansatz-env
                    [fixh fixargs] (e/get-app-fn-args (:fix fix-info))
                    tc-eq (doto (ansatz.kernel.TypeChecker. env') (.setFuel (long config/*default-fuel*)))
                    red-eq (.getReducer tc-eq)
                    eq-lvl (let [s (.inferType tc-eq ret-ansatz)]
                             (if (e/sort? s) (e/sort-level s) (lvl/succ lvl/zero)))
                    X2id (wf-fix-fresh) X2 (e/fvar X2id)
                    rawX2 (e/instantiate1 (:eqbody fix-info) X2)
                    ;; the equation LHS uses the user-facing n-ary application: unpack a
                    ;; Prod.mk-rooted pattern back into the argument list (defeq to the packed
                    ;; fix application by delta+beta)
                    unpack (fn [pattern]
                             (if (= 2 (:arity fix-info))
                               (let [[ph pas] (e/get-app-fn-args pattern)]
                                 (if (and (e/const? ph) (= "Prod.mk" (name/->string (e/const-name ph)))
                                          (= 4 (count pas)))
                                   [(nth pas 2) (nth pas 3)]
                                   (throw (ex-info "wf-fix eq: unsplit packed pattern" {}))))
                               [pattern]))
                    leaves (wf-fix-eq-leaves env' tc-eq red-eq rawX2 X2 [[X2id (:packed-ty fix-info)]])]
                (doseq [[i {:keys [fields pattern rhs]}] (map-indexed vector leaves)]
                  (let [ids (mapv first fields)
                        eq-core (e/app* (e/const' (name/from-string "Eq") [eq-lvl])
                                        ret-ansatz (apply e/app* (e/const' cname []) (unpack pattern)) rhs)
                        eq-type (loop [k (dec (count fields)) acc (e/abstract-many eq-core ids)]
                                  (if (< k 0) acc
                                      (recur (dec k) (e/forall' "x" (e/abstract-many (second (nth fields k)) (subvec ids 0 k)) acc :default))))
                        ;; WellFounded.Nat.fix -> Nat.fix_eq; WellFounded.fix (lex) -> fix_eq --
                        ;; both take the fix's own args plus the scrutinee
                        pf-core (apply e/app* (e/const' (name/from-string
                                                         (str (name/->string (e/const-name fixh)) "_eq"))
                                                        (vec (e/const-levels fixh)))
                                       (conj (vec fixargs) pattern))
                        pf (loop [k (dec (count fields)) acc (e/abstract-many pf-core ids)]
                             (if (< k 0) acc
                                 (recur (dec k) (e/lam "x" (e/abstract-many (second (nth fields k)) (subvec ids 0 k)) acc :default))))
                        eq-name (name/from-string (str fn-name ".eq_" (inc i)))]
                    (swap! ansatz-env env/check-constant (env/mk-thm eq-name [] eq-type pf))))
                (when *verbose*
                  (println (str "  ✓ " fn-name ".eq_1.." (count leaves) " equations (fix_eq)"))))
              (catch Exception e
                (when *verbose*
                  (println (str "  ⚠ wf-fix equation generation failed: " (.getMessage e))))))
            (try
              (let [env' @ansatz-env
                    ;; Build: ∀ params, fn(params) = body-with-fn
                    ;; Create fvars for params
                    fv-base 8300000
                    param-fvids (mapv #(+ fv-base %) (range n))
                    param-fvars (mapv e/fvar param-fvids)
                    ;; fn(params) applied
                    fn-applied (reduce e/app (e/const' cname []) param-fvars)
                    ;; fn-applied WHNF-reduces to the step body (fuel encoding), so Eq.refl works.
                    tc-eq (ansatz.kernel.TypeChecker. env')
                    _ (.setFuel tc-eq (long config/*default-fuel*))
                    _ (doseq [i (range n)]
                        (.addLocal tc-eq (long (nth param-fvids i))
                                   (str (first (nth pairs i)))
                                   (nth param-types i)))
                    rhs (.whnf (.getReducer tc-eq) fn-applied)
                    ;; Eq type: fn(args) = rhs — abstract the param fvars (a theorem must be
                    ;; CLOSED; leaving them raw was the old "Unknown free variable" failure)
                    eq-type (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                    ret-ansatz fn-applied rhs)
                    eq-type-abs (e/abstract-many eq-type param-fvids)
                    ;; Wrap in foralls
                    eq-full-type (loop [i (dec n) body eq-type-abs]
                                   (if (< i 0) body
                                       (recur (dec i)
                                              (e/forall' (str (first (nth pairs i)))
                                                         (nth param-types i) body :default))))
                    ;; Proof: Eq.refl (fn(args)) — works because fn(args) def-eq rhs
                    proof-core (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                       ret-ansatz fn-applied)
                    ;; Abstract fvars back to bvars
                    proof-abs (e/abstract-many proof-core param-fvids)
                    ;; Wrap in lambdas
                    proof-full (loop [i (dec n) body proof-abs]
                                 (if (< i 0) body
                                     (recur (dec i)
                                            (e/lam (str (first (nth pairs i)))
                                                   (nth param-types i) body :default))))
                    eq-name (name/from-string (str fn-name ".eq_unfold"))
                    eq-ci (env/mk-thm eq-name [] eq-full-type proof-full)]
                (swap! ansatz-env env/check-constant eq-ci)
                (when *verbose*
                  (println (str "  ✓ " fn-name ".eq_unfold equation theorem"))))
              (catch Exception e
                (when *verbose*
                  (println (str "  ⚠ equation theorem generation failed: " (.getMessage e)))))))

        ;; Compile to Clojure — uncurry for multi-arg
        clj-form (ansatz->clj @ansatz-env final-body [])
        ;; The compiled form is curried: (fn [p1] (fn [p2] ... body ...))
        ;; Wrap in uncurried version: (fn [p1 p2 ...] ((curried p1) p2) ...)
        ;; For multi-arg: create a function that accepts both curried and uncurried calls.
        ;; Curried: ((f x) y) — needed when called from other compiled code
        ;; Uncurried: (f x y) — needed for ergonomic Clojure usage
        clj-fn (if (<= n 1)
                 (eval clj-form)
                 (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) pairs)
                       curried-call (reduce (fn [f s] (list f s))
                                            (list clj-form (first param-syms))
                                            (rest param-syms))]
                   (eval
                     ;; Multi-arity: 1-arg returns curried, n-arg calls directly
                    `(fn
                       (~[(first param-syms)]
                         ;; Curried: return a fn that takes the remaining args
                        ~(if (= n 2)
                           `(fn [~(second param-syms)] ~curried-call)
                            ;; 3+ args: nested currying
                           (reduce (fn [body s] `(fn [~s] ~body))
                                   curried-call
                                   (reverse (rest param-syms)))))
                       (~param-syms ~curried-call)))))]
    clj-fn))

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
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
        ret-ansatz (sexp->ansatz env scope-full n ret-type-form)
        type-ansatz (loop [i (dec n) body ret-ansatz]
                      (if (< i 0) body
                          (let [[pn pt binfo] (nth pairs i)
                                s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                                ty (sexp->ansatz env s i pt)]
                            (recur (dec i) (e/forall' (str pn) ty body binfo)))))
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
        ptypes (mapv (fn [p] (sexp->ansatz env {} 0 (second p))) pairs)
        lctx (into {} (map (fn [fid p pt] [fid {:name (str (first p)) :type pt :tag :local}])
                           fids pairs ptypes))
        body-expr (elab/elaborate-in-context env lctx body-form)
        ;; abstract-many maps V[k] → bvar (len-1-k) (last → bvar 0), so pass fids in
        ;; param order (fids[0]=outermost param → highest bvar). Do NOT reverse.
        body-bvar (e/abstract-many body-expr fids)]
    (loop [i (dec n) acc body-bvar]
      (if (< i 0) acc
          (let [[pn _ binfo] (nth pairs i)]
            (recur (dec i) (e/lam (str pn) (nth ptypes i) acc (or binfo :default))))))))

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
(clojure.core/defn define-verified
  "Define a verified function. Auto-detects structural recursion; if the recursion is not
   structural, tries lean4's GuessLex (single Nat measure) and redirects to well-founded
   recursion when a decreasing measure is found. Returns the compiled Clojure fn."
  [fn-name params ret-type-form body-form]
  (try
    (define-verified-impl fn-name params ret-type-form body-form)
    (catch clojure.lang.ExceptionInfo e
      (if (= ::redirect-wf (:kind (ex-data e)))
        (define-verified-wf fn-name params ret-type-form body-form (:measure (ex-data e)))
        (throw e)))))

(clojure.core/defn- define-verified-impl
  "Structural-recursion path. Throws {:kind ::redirect-wf :measure m} when recursion is
   non-structural but a WF measure was synthesized (handled by define-verified)."
  [fn-name params ret-type-form body-form]
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)
        cname (name/from-string (str fn-name))
        ;; Build type ∀ params → ret-type up front (the self-axiom below needs it).
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
        ret-ansatz (sexp->ansatz env scope-full n ret-type-form)
        type-ansatz (loop [i (dec n) body ret-ansatz]
                      (if (< i 0) body
                          (let [[pn pt binfo] (nth pairs i)
                                s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                                ty (sexp->ansatz env s i pt)]
                            (recur (dec i) (e/forall' (str pn) ty body binfo)))))
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
        body-ansatz (binding [surface-match/*self-name* cname
                              surface-match/*self-params* (vec (range 1 (inc n)))]
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
                           "structurally decreasing on a parameter, and no Nat measure was found to be "
                           "decreasing. Add `:termination-by <measure>` for well-founded recursion, or "
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
                      n-non-discr (dec n)]
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
                            ;; Get actual inductive type params from recursor args
                            rec-args (vec (e/get-app-args peeled))
                            ind-type-params (vec (take np rec-args))
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
                            ;; Non-discriminant param indices (all except discr-pos)
                            non-discr-indices (vec (remove #{discr-pos} (range n)))
                            ;; Register fvars in TC's lctx for WHNF reduction
                            param-types (mapv (fn [j]
                                                (let [orig-idx (nth non-discr-indices j)
                                                      [pn pt-form] (nth (vec pairs) orig-idx)]
                                                  (sexp->ansatz env'
                                                                (into {} (map-indexed (fn [k [p _]] [p k]) (take orig-idx (vec pairs))))
                                                                orig-idx pt-form)))
                                              (range n-non-discr))
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
                                                                           (when *verbose* (println "  aux eq_" (inc ci-idx) "for" aux-name-str))))
                                                                       (catch Exception ex
                                                                         (when *verbose*
                                                                           (println "  aux eq_" (inc ci-idx) "for" aux-name-str "FAILED:" (.getMessage ex))
                                                                           (.printStackTrace ex *out*))))))
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
                                                ret-ansatz lhs rhs)
                                eq-body (if condition (e/arrow condition eq-body) eq-body)
                                abstracted-type
                                (e/abstract-many eq-body (vec (concat param-fvids all-fvids)))
                                ;; Wrap in foralls: all fields then params (right to left)
                                full-type (loop [j (dec all-nf) body abstracted-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                                  (nth all-ftypes j) body :default))))
                                full-type (loop [j (dec n-non-discr) body full-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                                  (nth param-types j) body :default))))
                                ;; Proof: rfl (with fvars), then abstract
                                rfl-proof (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                  ret-ansatz lhs)
                                proof-body (if condition (e/lam "h" condition rfl-proof :default) rfl-proof)
                                abstracted-proof (e/abstract-many proof-body
                                                                  (vec (concat param-fvids all-fvids)))
                                full-proof (loop [j (dec all-nf) body abstracted-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (if (< j nf) (str "f" j) (str "g" (- j nf)))
                                                               (nth all-ftypes j) body :default))))
                                full-proof (loop [j (dec n-non-discr) body full-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (str (first (nth (vec pairs) (nth non-discr-indices j))))
                                                               (nth param-types j) body :default))))
                                eqn-name (name/from-string (str fn-name ".eq_" (inc i) (or suffix "")))]
                            (try
                              (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "type:" (e/->string full-type)))
                              (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                (.setFuel tc-v (int config/*default-fuel*))
                                (.inferType tc-v full-proof)
                                (swap! ansatz-env env/check-constant (env/mk-thm eqn-name [] full-type full-proof))
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) ":" (e/->string full-type))))
                              (catch Exception e
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "skipped:" (.getMessage e))))))))
                      (catch Exception e
                        (when *verbose* (println "  eq" (inc i) "gen failed:" (.getMessage e)))))))))
            (catch Exception ex
              (when *verbose* (println "  eq-gen outer:" (.getMessage ex)))))
        ;; Optimizer seam: a runtime (wandler) may rewrite the body to a kernel-EQUAL, faster term
        ;; just for codegen — the original stays the proven definition in the env.
        runtime-body (if-let [opt @optimize-hook]
                       (or (opt @ansatz-env body-ansatz) body-ansatz)
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
         pairs (parse-params params)
         n (count pairs)
         scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
         ;; Bind *scope-types* so that auto-elaborate can infer implicit args
         ;; from parameter types (Lean 4: elaborator has full context)
         scope-types-map (into {} (map-indexed
                                   (fn [i [pn pt-form]]
                                     (let [s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))]
                                       [pn (sexp->ansatz env s i pt-form)]))
                                   pairs))
         prop-ansatz (binding [*scope-types* scope-types-map]
                       (sexp->ansatz env scope-full n prop-form))
         goal-type (loop [i (dec n) body prop-ansatz]
                     (if (< i 0) body
                         (let [[pn pt binfo] (nth pairs i)
                               s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                               ty (sexp->ansatz env s i pt)]
                           (recur (dec i) (e/forall' (str pn) ty body binfo)))))
         [ps _] (proof/start-proof env goal-type)
         ps (if (seq pairs) (basic/intros ps (mapv (comp str first) pairs)) ps)
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

;; ============================================================
;; Macros
;; ============================================================

;; ============================================================
;; Public macros — clean names (preferred) and legacy c-prefixed
;; ============================================================

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
        ret-type (if meta? (binder-type fn-name) (first more))
        body-and-opts (if meta? more (rest more))
        [opts body] (if (= :termination-by (first body-and-opts))
                      [{:termination-by (second body-and-opts)} (nth body-and-opts 2)]
                      [{} (first body-and-opts)])
        partial? (:partial (meta fn-name))
        nm (vary-meta fn-name dissoc :- :tag :partial)]
    (cond
      partial?
      `(def ~nm (define-partial '~nm '~params '~ret-type '~body))
      (:termination-by opts)
      `(def ~nm (define-verified-wf '~nm '~params '~ret-type '~body '~(:termination-by opts)))
      :else
      `(def ~nm (define-verified '~nm '~params '~ret-type '~body)))))

(defmacro theorem
  "Prove a theorem.
   (a/theorem add-zero [n :- Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))"
  [thm-name params prop & tactics]
  `(prove-theorem '~thm-name '~params '~prop '~(vec tactics)))

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

(defmacro structure
  "Define a structure (single-constructor inductive with projections).

   (a/structure Pair [α Type β Type] (fst α) (snd β))

   Fields are specified as (name type) pairs. The constructor is always 'mk'.
   Projection functions are automatically generated."
  [type-name params & fields]
  (let [;; Split :in option
        [opts fields] (if (= :in (first fields))
                        [{:in (second fields)} (drop 2 fields)]
                        [{} fields])
        ;; Parse fields: (name type) pairs
        field-specs (mapv (fn [f]
                            (if (sequential? f)
                              [(first f) (second f)]
                              (throw (ex-info "structure field must be (name type)" {:field f}))))
                          fields)
        ;; Build the flat field vector for the constructor: [name1 type1 name2 type2 ...]
        flat-fields (vec (mapcat identity field-specs))
        ;; Single constructor named 'mk'
        ctor-spec ['mk flat-fields]]
    `(do
       ;; Define the inductive with single constructor
       (inductive/define-inductive (env) ~(str type-name) '~params '~[ctor-spec]
         ~@(when (:in opts) [:in `'~(:in opts)]))

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

       ;; Emit Clojure defrecord for runtime representation
       ;; The record has keyword-accessible fields: (:x point), (:y point)
       (defrecord ~type-name ~(mapv (fn [[fname _]] (symbol (str fname))) field-specs))

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
