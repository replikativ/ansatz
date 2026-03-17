;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Verified Clojure programming via Ansatz.
;;
;; Write Clojure functions with Ansatz types. Prove properties. Run at native speed.
;;
;; (ansatz/init! "path/to/store" "branch")
;; (ansatz/defn double [n Nat] Nat (+ n n))
;; (ansatz/theorem add-zero [n Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))
;; (double 21)  ;; => 42, native speed

(ns ansatz.core
  "Verified Clojure — write proven programs using Ansatz types and tactics."
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
            [ansatz.inductive :as inductive]
            [ansatz.surface.match :as surface-match]
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

(defn make-context
  "Create a fresh ProofContext from an env and instance index."
  [env instance-index]
  (->ProofContext env instance-index (atom {})))

(defn fork-context
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

(defn init!
  "Load Ansatz environment from LMDB store and build instance index."
  [store-path branch]
  (let [sm (storage/open-store store-path)
        ctx (storage/prepare-verify sm branch)
        env (:env ctx)]
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

(defn env [] (or @ansatz-env (throw (ex-info "Call (ansatz/init!) first" {}))))
(defn instance-index [] (or @ansatz-instance-index {}))

(declare synth-cache)

(defn context
  "Get the current global ProofContext (built from global atoms)."
  []
  (->ProofContext (env) (instance-index) @(resolve 'ansatz.core/synth-cache)))

;; ============================================================
;; Instance resolution (name-based, works with PSS env)
;; ============================================================

(defn resolve-basic-instance
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

(defn- try-synthesize-instance
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

(defn- auto-elaborate
  "Auto-elaborate a function application by inserting implicit and
   instance-implicit arguments. Walks the function's forall telescope:
   - {implicit} → try to infer from later unification, use placeholder for now
   - [inst-implicit] → synthesize via TC resolution
   - (explicit) → consume next user argument
   This is the core of Lean 4's App.lean elaboration loop."
  [env head-fn fn-type user-args]
  (let [;; First instantiate level params with zero (default heuristic)
        ^ConstantInfo ci (env/lookup env (e/const-name head-fn))
        lparams (when ci (vec (.levelParams ci)))
        level-subst (when (seq lparams) (zipmap lparams (repeat lvl/zero)))
        fn-type (if level-subst
                  (e/instantiate-level-params fn-type level-subst)
                  fn-type)]
    (loop [f head-fn
           ftype fn-type
           args user-args
           ;; Track implicit mvars for later unification
           implicit-slots []]
      (if (e/forall? ftype)
        (let [binfo (e/forall-info ftype)
              btype (e/forall-type ftype)
              body (e/forall-body ftype)]
          (case binfo
            ;; Explicit parameter: consume next user arg
            :default
            (if (seq args)
              (let [arg (first args)]
                (recur (e/app f arg)
                       (e/instantiate1 body arg)
                       (vec (rest args))
                       implicit-slots))
              ;; No more args — partial application, return what we have
              f)

            ;; Implicit: try to infer from user args by matching types.
            ;; Simple heuristic: if a user arg has the same type as what's
            ;; expected, use it. Otherwise leave as a hole that the kernel
            ;; will fill via def-eq during type checking.
            (:implicit :strict-implicit)
            (let [;; Try to find a matching user arg by type
                  ;; For now, use a simple heuristic: if the binder type is
                  ;; a Sort (i.e., the param is a type), look for user args
                  ;; that ARE types and try them.
                  ;; Fallback: use the first explicit arg's inferred type.
                  st (tc/mk-tc-state env)
                  btype-whnf (try (#'tc/cached-whnf st btype) (catch Exception _ btype))
                  arg-val
                  (cond
                    ;; Type parameter (Sort u): use first arg if it's a type,
                    ;; otherwise infer its type
                    (e/sort? btype-whnf)
                    (when (seq args)
                      (let [arg (first args)
                            arg-ty (try (tc/infer-type st arg) (catch Exception _ nil))]
                        (if (and arg-ty (e/sort? arg-ty))
                          arg  ;; arg IS a type (e.g., Real : Sort 1) → use directly
                          arg-ty)))  ;; arg is a value → use its type
                    :else nil)]
              (if arg-val
                (recur (e/app f arg-val)
                       (e/instantiate1 body arg-val)
                       args
                       implicit-slots)
                ;; Can't infer — skip this param and hope the kernel handles it
                ;; Use a placeholder that will trigger an error if not resolved
                (recur (e/app f btype) ;; use the type itself as placeholder
                       (e/instantiate1 body btype)
                       args
                       (conj implicit-slots {:idx (count implicit-slots) :type btype}))))

            ;; Instance-implicit: synthesize via TC
            :inst-implicit
            (let [inst (try-synthesize-instance env btype)]
              (if inst
                (recur (e/app f inst)
                       (e/instantiate1 body inst)
                       args
                       implicit-slots)
                ;; Can't synthesize — leave as placeholder
                (recur (e/app f btype)
                       (e/instantiate1 body btype)
                       args
                       implicit-slots)))))
        ;; Not a forall — apply remaining user args directly
        (reduce e/app f args)))))

(defn- resolve-hop-instance
  "Build the full H-operator instance: instHOp α (basic-inst).
   hop-name: 'HAdd', 'HMul', etc.
   basic-class: 'Add', 'Mul', etc."
  [env hop-name basic-class type-name-str type-expr]
  (when-let [basic-inst (resolve-basic-instance env basic-class type-name-str type-expr)]
    (let [inst-hop-name (str "inst" hop-name)]
      (when-let [ci (env/lookup env (name/from-string inst-hop-name))]
        (e/app* (e/const' (name/from-string inst-hop-name) [lvl/zero])
                type-expr basic-inst)))))

(defn- build-binop
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

(declare sexp->ansatz)

;; Type context for outer-scope variables — used by match handler to
;; register fvars in the tc's local context. Maps symbol → Expr (type).
;; Set by build-telescope when compiling function bodies.
(def ^:dynamic *scope-types* {})

(defn- build-telescope
  "Build nested foralls or lambdas from param pairs.
   ctor: e/forall' or e/lam."
  [env scope depth pairs body-form ctor]
  (if (empty? pairs)
    (sexp->ansatz env scope depth body-form)
    (let [[pname ptype-form] (first pairs)
          ptype (sexp->ansatz env scope depth ptype-form)
          new-scope (assoc scope pname depth)
          body (binding [*scope-types* (assoc *scope-types* pname ptype)]
                 (build-telescope env new-scope (inc depth) (rest pairs) body-form ctor))]
      (ctor (str pname) ptype body :default))))

(defn sexp->ansatz
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
    ;; Handle Clojure nil → Ansatz empty list (most common use)
       (nil? form) (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                          (e/const' (name/from-string "Nat") []))
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
                                (e/const' (name/from-string "Nat") []))
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

       (and (sequential? form) (seq form))
    ;; Check custom elaborator registry first
       (if-let [elab-fn (get @elaborator-registry (first form))]
         (elab-fn env scope depth (vec (rest form)) lctx)
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
                   class-name (if (= h "le") "LE" "LT")
                   inst (try-synthesize-instance env
                                                 (e/app (e/const' (name/from-string class-name) [lvl/zero]) type-expr))]
               (if inst
                 (e/app* (e/const' (name/from-string (str class-name "." h)) [lvl/zero])
                         type-expr inst a b)
                 (throw (ex-info (str "No " class-name " instance for " type-name) {}))))

        ;; Binders
             "forall" (build-telescope env scope depth
                                       (partition 2 (remove #{:-} (nth form 1))) (nth form 2) e/forall')
             ("fn" "lam") (build-telescope env scope depth
                                           (partition 2 (remove #{:-} (nth form 1))) (nth form 2) e/lam)
             ("->" "arrow") (e/arrow (sexp->ansatz env scope depth (nth form 1))
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

        ;; cons/nil for lists (Clojure-safe names for List.cons/List.nil)
             "cons" (let [nat (e/const' (name/from-string "Nat") [])
                          x (sexp->ansatz env scope depth (nth form 1))
                          s (sexp->ansatz env scope depth (nth form 2))]
                      (e/app* (e/const' (name/from-string "List.cons") [lvl/zero]) nat x s))
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
                               (sexp->ansatz env {} 0 sexpr all-lctx)))
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
                 (auto-elaborate env head-fn (.type ci) (vec user-args))
            ;; Not a known constant — just apply directly
                 (reduce e/app compiled))))))

       :else (throw (ex-info (str "Cannot compile: " form) {:form form}))))))

;; ============================================================
;; Ansatz Expr → Clojure form compiler
;; ============================================================

(defn ansatz->clj
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
            "HAdd.hAdd" (list '+ (nth ca 4) (nth ca 5))
            "HMul.hMul" (list '* (nth ca 4) (nth ca 5))
            "HSub.hSub" (list 'max 0 (list '- (nth ca 4) (nth ca 5)))
            "HDiv.hDiv" (list 'quot (nth ca 4) (nth ca 5))
            "HPow.hPow" (list 'long (list 'Math/pow (nth ca 4) (nth ca 5)))
            "Nat.add" (list '+ (nth ca 0) (nth ca 1))
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
            ;; Constructor application → tagged vector [field1 field2 ...]
            ;; Skip type params, keep only fields
            (if-let [ctor-ci (when-let [ci (env/lookup env (e/const-name head))]
                               (when (.isCtor ^ConstantInfo ci) ci))]
              (let [np (.numParams ctor-ci)
                    nf (.numFields ctor-ci)
                    fields (subvec ca np (+ np nf))]
                (if (zero? nf)
                  ;; 0-field ctor: use index for enum dispatch
                  (let [cidx (.cidx ctor-ci)]
                    (if (zero? cidx) nil cidx))
                  (vec fields)))
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
                      (if has-rec
                        (list 'letfn [(list self-sym [t-sym] body)]
                              (list self-sym major))
                      ;; Non-recursive: just apply directly
                        (list 'let [t-sym major] body)))))
            ;; User-defined function: curried application
                (reduce (fn [f a] (list f a)) (symbol h) ca)))))
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

(defn register-tactic!
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

(defn register-elaborator!
  "Register a custom elaboration form for sexp->ansatz.

   Example:
     (a/register-elaborator! 'my-form
       (fn [env scope depth args lctx]
         ;; args: the arguments after the form name
         ;; Return: an Expr (kernel expression)
         (let [a (sexp->ansatz env scope depth (first args) lctx)]
           (e/app (e/const' (name/from-string \"MyFn\") []) a))))

   Then use in definitions:
     (a/defn f [x :- Nat] Nat (my-form x))"
  [name f]
  (swap! elaborator-registry assoc name f))

(defn register-simproc!
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
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/rewrite ps (e/fvar fid))))
   'cases     (fn [ps args]
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/cases ps fid)))
   'induction (fn [ps args]
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
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
   'solve_by_elim (fn [ps _args] (basic/solve-by-elim ps))
   'split_ifs (fn [ps _args] (basic/split-ifs ps))
   'revert    (fn [ps args]
                (let [fid (some (fn [[id d]] (when (= (str (first args)) (:name d)) id))
                                (:lctx (proof/current-goal ps)))]
                  (basic/revert ps fid)))})

;; Initialize registry with built-in tactics
(when (empty? @tactic-registry)
  (reset! tactic-registry builtin-tactics))

(defn run-tactic [ps tac]
  (let [registry @tactic-registry]
    (if (symbol? tac)
      (if-let [f (get registry tac)] (f ps nil)
              (throw (ex-info (str "Unknown tactic: " tac) {:available (keys registry)})))
      (let [[name & args] tac]
        (if-let [f (get registry name)] (f ps (vec args))
                (throw (ex-info (str "Unknown tactic: " name) {:available (keys registry)})))))))

;; ============================================================
;; Public API
;; ============================================================

(defn define-verified
  "Define a verified function. Returns compiled Clojure fn."
  [fn-name params ret-type-form body-form]
  (let [env (env)
        pairs (partition 2 (remove #{:-} params))
        body-ansatz (build-telescope env {} 0 pairs body-form e/lam)
        ;; Build type: ∀ params → ret-type
        n (count (vec pairs))
        scope-full (into {} (map-indexed (fn [i [p _]] [p i]) (vec pairs)))
        ret-ansatz (sexp->ansatz env scope-full n ret-type-form)
        type-ansatz (loop [i (dec n) body ret-ansatz]
                      (if (< i 0) body
                          (let [[pn pt] (nth (vec pairs) i)
                                s (into {} (map-indexed (fn [j [p _]] [p j]) (take i (vec pairs))))
                                ty (sexp->ansatz env s i pt)]
                            (recur (dec i) (e/forall' (str pn) ty body :default)))))
        ;; Type-check
        tc (ansatz.kernel.TypeChecker. env)
        _ (.inferType tc body-ansatz)
        ;; Add to environment
        cname (name/from-string (str fn-name))
        ci (env/mk-def cname [] type-ansatz body-ansatz)
        _ (reset! ansatz-env (env/add-constant env ci))
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
                            ;; Build ctor-app and LHS with fvars
                            ctor-app (reduce e/app (e/const' ctor-name ctor-levels)
                                             (concat ind-type-params field-fvars))
                            lhs (reduce e/app (e/const' cname []) (concat param-fvars [ctor-app]))
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
                            ;; Register fvars in TC's lctx for WHNF reduction
                            param-types (mapv (fn [j]
                                                (let [[pn pt-form] (nth (vec pairs) j)]
                                                  (sexp->ansatz env'
                                                                (into {} (map-indexed (fn [k [p _]] [p k]) (take j (vec pairs))))
                                                                j pt-form)))
                                              (range n-non-discr))
                            st' (reduce (fn [s [fid nm tp]]
                                          (update s :lctx red/lctx-add-local fid nm tp))
                                        (tc/mk-tc-state env')
                                        (concat (map vector param-fvids
                                                     (map #(str (first (nth (vec pairs) %))) (range n-non-discr))
                                                     param-types)
                                                (map vector field-fvids
                                                     (map #(str "f" %) (range nf))
                                                     field-types)))
                            ;; WHNF-reduce LHS → RHS (with fvars)
                            rhs-raw (#'tc/cached-whnf st' lhs)
                            ;; Generate unconditional equation: f args = WHNF(f args)
                            ;; If WHNF result has stuck Bool.rec, that's OK — the equation
                            ;; still holds by rfl. The Bool.rec splitting is handled by
                            ;; simp + split_ifs later.
                            equations [{:rhs rhs-raw :condition nil :suffix nil}]]
                        ;; Build and register each equation using abstract-many
                        (doseq [[_ {:keys [rhs condition suffix]}] (map-indexed vector equations)]
                          (let [;; Eq ret_type lhs rhs (all with fvars)
                                eq-body (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                                ret-ansatz lhs rhs)
                                eq-body (if condition (e/arrow condition eq-body) eq-body)
                                ;; Abstract all fvars to bvars in one pass (correct depth handling)
                                ;; Order: outermost (first param) to innermost (last field)
                                ;; Lean 4: xs in telescope order (outermost first)
                                ;; abstract: xs[0]→bvar(n-1), xs[n-1]→bvar(0)
                                ;; foldRev wrap: xs[n-1] first → ... → xs[0] last (outermost)
                                abstracted-type
                                (e/abstract-many eq-body (vec (concat param-fvids field-fvids)))
                                ;; Wrap in foralls: fields then params (right to left)
                                full-type (loop [j (dec nf) body abstracted-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (str "f" j)
                                                                  (nth field-types j) body :default))))
                                full-type (loop [j (dec n-non-discr) body full-type]
                                            (if (< j 0) body
                                                (recur (dec j)
                                                       (e/forall' (str (first (nth (vec pairs) j)))
                                                                  (nth param-types j) body :default))))
                                ;; Proof: rfl (with fvars), then abstract
                                rfl-proof (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                  ret-ansatz lhs)
                                proof-body (if condition (e/lam "h" condition rfl-proof :default) rfl-proof)
                                abstracted-proof (e/abstract-many proof-body
                                                                  (vec (concat param-fvids field-fvids)))
                                full-proof (loop [j (dec nf) body abstracted-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (str "f" j) (nth field-types j) body :default))))
                                full-proof (loop [j (dec n-non-discr) body full-proof]
                                             (if (< j 0) body
                                                 (recur (dec j)
                                                        (e/lam (str (first (nth (vec pairs) j)))
                                                               (nth param-types j) body :default))))
                                eqn-name (name/from-string (str fn-name ".eq_" (inc i) (or suffix "")))]
                            (try
                              (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "type:" (e/->string full-type)))
                              (let [tc-v (ansatz.kernel.TypeChecker. @ansatz-env)]
                                (.setFuel tc-v (int config/*default-fuel*))
                                (.inferType tc-v full-proof)
                                (reset! ansatz-env (env/add-constant @ansatz-env (env/mk-thm eqn-name [] full-type full-proof)))
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) ":" (e/->string full-type))))
                              (catch Exception e
                                (when *verbose* (println "  eq_" (str (inc i) (or suffix "")) "skipped:" (.getMessage e))))))))
                      (catch Exception e
                        (when *verbose* (println "  eq" (inc i) "gen failed:" (.getMessage e)))))))))
            (catch Exception ex
              (when *verbose* (println "  eq-gen outer:" (.getMessage ex)))))
        ;; Compile to Clojure
        clj-form (ansatz->clj @ansatz-env body-ansatz [])
        clj-fn (eval clj-form)]
    (when *verbose* (println "✓" fn-name ":" (pr-str clj-form)))
    clj-fn))

(defn prove-theorem
  "Prove a theorem. Returns nil (side-effect: adds to env).
   Optional ctx: ProofContext for isolated proving (no global mutation)."
  ([thm-name params prop-form tactic-forms]
   (prove-theorem thm-name params prop-form tactic-forms nil))
  ([thm-name params prop-form tactic-forms ctx]
   (let [env (if ctx (:env ctx) (env))
         pairs (vec (partition 2 (remove #{:-} params)))
         n (count pairs)
         scope-full (into {} (map-indexed (fn [i [p _]] [p i]) pairs))
         prop-ansatz (sexp->ansatz env scope-full n prop-form)
         goal-type (loop [i (dec n) body prop-ansatz]
                     (if (< i 0) body
                         (let [[pn pt] (nth pairs i)
                               s (into {} (map-indexed (fn [j [p _]] [p j]) (take i pairs)))
                               ty (sexp->ansatz env s i pt)]
                           (recur (dec i) (e/forall' (str pn) ty body :default)))))
         [ps _] (proof/start-proof env goal-type)
         ps (if (seq pairs) (basic/intros ps (mapv (comp str first) pairs)) ps)
         ps (reduce run-tactic ps tactic-forms)]
     (when-not (proof/solved? ps)
       (throw (ex-info (str "Proof incomplete\n" (proof/format-goals ps)) {:ps ps})))
     (extract/verify ps)
     (let [term (extract/extract ps)
           cname (name/from-string (str thm-name))
           ci (env/mk-thm cname [] goal-type term)]
       ;; When using a context, mutate the context's env (mutable Java Env)
       ;; When using global, mutate the global atom
       (if ctx
         (env/add-constant (:env ctx) ci)
         (reset! ansatz-env (env/add-constant env ci))))
     (when *verbose* (println "✓" thm-name "proved")))))

;; ============================================================
;; Macros
;; ============================================================

;; ============================================================
;; Public macros — clean names (preferred) and legacy c-prefixed
;; ============================================================

(defmacro defn
  "Define a verified function. Use qualified: (a/defn double [n :- Nat] Nat (+ n n))"
  [fn-name params ret-type body]
  `(def ~fn-name (define-verified '~fn-name '~params '~ret-type '~body)))

(defmacro theorem
  "Prove a theorem.
   (a/theorem add-zero [n :- Nat] (= Nat (+ n 0) n) (simp Nat.add_zero))"
  [thm-name params prop & tactics]
  `(prove-theorem '~thm-name '~params '~prop '~(vec tactics)))

(defmacro inductive
  "Define an inductive type with constructors.
   (a/inductive Color [] (red) (green) (blue))

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
        ctors body
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
        ctor-specs (mapv parse-ctor ctors)]
    `(do (inductive/define-inductive (env) ~(str type-name) '~params '~ctor-specs
           ~@(when (:in opts) [:in `'~(:in opts)])
           ~@(when (:indices opts) [:indices `'~(:indices opts)]))
         nil)))

