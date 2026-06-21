;; Tactic layer — ac_rfl: associative/commutative normalization by REFLECTION.
;;
;; Faithful port of Lean 4's `ac_rfl` (`../lean4/src/Lean/Meta/Tactic/AC/Main.lean`) onto the
;; verified core `Lean.Data.AC` (`../lean4/src/Init/Data/AC.lean`, already in our store). The heavy
;; lifting is the kernel-CHECKED normalizer `Lean.Data.AC.norm` whose correctness theorem
;;   `Context.eq_of_norm : (norm ctx a == norm ctx b) = true → eval α ctx a = eval α ctx b`
;; is proven once. This tactic is the META/reflection layer: it reifies an equation goal `l = r`
;; into a `Data.AC.Expr` over abstract atoms, synthesizes the `Std.Associative` (required) /
;; `Commutative` / `IdempotentOp` / `LawfulIdentity` (optional) instances for the operator, builds a
;; `Context`, and emits `eq_of_norm … (Eq.refl Bool.true)` as the proof. SOUNDNESS rests entirely on
;; the kernel: it independently reduces `norm a == norm b ≡ true` and `eval a ≡ l`, `eval b ≡ r`.
;;
;; Unlike Lean's simp-post traversal (which normalizes each maximal AC-subterm in place to support
;; `ac_nf`), this is the equation-goal specialization: we reify the WHOLE `l = r` over one shared
;; atom map and emit ONE `eq_of_norm` at the goal. That is exactly the shape the algebraic laws need
;; (a monoid/semiring reassociation `(a⊕b)⊕c = a⊕(b⊕c)`, identity absorption `a⊕0 = a`, …) and keeps
;; the port small. Non-equation goals, or equations whose two sides are not AC-equal, fail cleanly.

(ns ansatz.tactic.ac
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.instance :as inst])
  (:import [ansatz.kernel Expr]))

(defn- C [s ls] (e/const' (nm/from-string s) ls))
(def ^:private z lvl/zero)
(def ^:private one (lvl/succ lvl/zero))

;; ── instance provisioning ───────────────────────────────────────────────────────────────────────
;; Mirrors Lean's `Lean.Meta.AC.getInstance` (which consults `synthInstance`). We try the faithful
;; `ansatz.tactic.instance/synthesize*` FIRST; PSS instance synthesis is name-fragile for multi-arg
;; outParam classes (e.g. `LawfulIdentity op o`), so domains that own an operator may also register a
;; deterministic builder here. A provider is `{:assoc :comm :idem :identity}`, each a fn — `:assoc`/
;; `:comm`/`:idem` take `[carrier op]` → instance term (or nil), and `:identity` takes
;; `[carrier op atom]` → a `LawfulIdentity op atom` instance term when `atom` is the operator's
;; neutral element, else nil. Keyed by the operator's head-constant name (e.g. "WAddMonoid.add").
(defonce ac-providers (atom {}))

(defn register-ac-op!
  "Register an AC instance provider for the operator whose head constant is `op-head` (a string).
   See `ac-providers` for the provider shape."
  [op-head provider]
  (swap! ac-providers assoc op-head provider))

(defn- op-head [op]
  (let [[h _] (e/get-app-fn-args op)] (when (e/const? h) (nm/->string (e/const-name h)))))

(defn- synth?
  "Try to synthesize an instance of `goal` (a class application). Returns the instance term or nil."
  [st env index goal]
  (try (inst/synthesize* st env index goal 0) (catch Throwable _ nil)))

(defn- get-inst
  "Get a `class` instance for `op` (carrier `α`, level `u`): faithful synthesis first, then the
   registered provider's `field` builder. `args` are extra class args after the carrier."
  [st env index class field carrier u op & args]
  (or (synth? st env index (apply e/app* (C class [u]) carrier op args))
      (when-let [f (get (get @ac-providers (op-head op)) field)]
        (apply f carrier op args))))

;; ── reflection data: PreContext (op + its algebra instances) ─────────────────────────────────────
(defn- pre-context
  "The AC algebra for operator `op : α → α → α` (carrier `α`, level `u`). Returns
   {:op :u :carrier :assoc :comm :idem} or nil if `op` is not even associative (so nothing to do).
   Mirrors `Lean.Meta.AC.preContext`: Associative is required; Commutative/IdempotentOp are optional."
  [st env index op carrier u]
  (when-let [assoc (get-inst st env index "Std.Associative" :assoc carrier u op)]
    {:op op :u u :carrier carrier :assoc assoc
     :comm (get-inst st env index "Std.Commutative" :comm carrier u op)
     :idem (get-inst st env index "Std.IdempotentOp" :idem carrier u op)}))

;; ── reification: term tree under `op` → Data.AC.Expr over a shared atom map ───────────────────────
(defn- as-bin
  "If `t` is `op a b` (head def-eq `op`, exactly two trailing args), return [a b]; else nil. Faithful
   to Lean's `bin op l r = app (app op l) r` recognized via `isDefEq op op₂`."
  [st op t]
  (when (e/app? t)
    (let [f1 (e/app-fn t)]
      (when (e/app? f1)
        (when (try (tc/is-def-eq st op (e/app-fn f1)) (catch Throwable _ false))
          [(e/app-arg f1) (e/app-arg t)])))))

(defn- atom-index!
  "Find `t`'s index in the shared atoms vector (dedup by structural equality, like Lean's ExprSet),
   adding it if new. `atoms` is an atom holding a vector of Expr."
  [atoms t]
  (let [v @atoms
        i (first (keep-indexed (fn [i a] (when (.equals ^Object a ^Object t) i)) v))]
    (or i (do (swap! atoms conj t) (count v)))))

(def ^:private ac-evar (C "Lean.Data.AC.Expr.var" []))
(def ^:private ac-eop  (C "Lean.Data.AC.Expr.op" []))

(defn- reify-side
  "Reify term `t` into a `Data.AC.Expr` term, collecting atoms into `atoms`."
  [st op atoms t]
  (if-let [[a b] (as-bin st op t)]
    (e/app* ac-eop (reify-side st op atoms a) (reify-side st op atoms b))
    (e/app ac-evar (e/lit-nat (atom-index! atoms t)))))

;; ── faithful Clojure port of `Lean.Data.AC.norm` (for the gating check / clean failure) ──────────
;; norm operates on our *reified* Data.AC.Expr terms; decode structurally instead of via the kernel.
(defn- decode-toList [t]
  (let [[h args] (e/get-app-fn-args t)]
    (condp = (and (e/const? h) (nm/->string (e/const-name h)))
      "Lean.Data.AC.Expr.var" [(e/lit-nat-val (first args))]
      "Lean.Data.AC.Expr.op"  (into (decode-toList (first args)) (decode-toList (second args)))
      (throw (ex-info "ac: malformed reified Expr" {:t (e/->string t)})))))

(defn- norm-list
  "Port of `Lean.Data.AC.norm`: toList → removeNeutrals → (sort if comm) → (mergeIdem if idem)."
  [idxs neutral? comm? idem?]
  (let [;; removeNeutrals: drop neutral indices; if that empties a non-empty list, keep its head.
        rm (let [ys (vec (remove neutral? idxs))]
             (if (and (seq idxs) (empty? ys)) [(first idxs)] ys))
        sorted (if comm? (vec (sort rm)) rm)
        merged (if idem? (->> sorted (partition-by identity) (map first) vec) sorted)]
    merged))

;; ── PLift/Option helpers for the Context fields ──────────────────────────────────────────────────
(defn- plift [t] (e/app (C "PLift" [z]) t))
(defn- opt-field
  "Build `Option (PLift cls)`: `some (PLift cls) (PLift.up cls inst)` when `inst` present, else
   `none (PLift cls)`. `cls` is a Prop, so all `PLift`/`Option` levels are 0."
  [cls inst]
  (if inst
    (e/app* (C "Option.some" [z]) (plift cls) (e/app* (C "PLift.up" [z]) cls inst))
    (e/app (C "Option.none" [z]) (plift cls))))

(defn ac-rfl-term
  "Core: given proof-state `ps`, build the `eq_of_norm` proof term closing the current `=` goal by AC
   normalization, or throw a tactic error. Returns the proof Expr. Pure w.r.t. `ps` (no mutation)."
  [ps]
  (let [env (:env ps)
        g (proof/current-goal ps)
        _ (when-not g (throw (ex-info "ac_rfl: no goals" {})))
        st (tc/attach-lctx (tc/mk-tc-state env) (:lctx g))
        index (inst/build-instance-index env)
        [h args] (e/get-app-fn-args (:type g))
        _ (when-not (and (e/const? h) (= "Eq" (nm/->string (e/const-name h))) (= 3 (count args)))
            (throw (ex-info "ac_rfl: goal is not an equality" {:goal (e/->string (:type g))})))
        carrier (nth args 0)
        L (nth args 1)
        R (nth args 2)
        u (e/sort-level (red/whnf env (tc/infer-type st carrier) (:lctx g)))
        ;; operator: strip two trailing args off whichever side is op-headed.
        op (or (when (and (e/app? L) (e/app? (e/app-fn L))) (e/app-fn (e/app-fn L)))
               (when (and (e/app? R) (e/app? (e/app-fn R))) (e/app-fn (e/app-fn R)))
               (throw (ex-info "ac_rfl: neither side is a binary operator application" {})))
        pc (or (pre-context st env index op carrier u)
               (throw (ex-info "ac_rfl: operator has no Std.Associative instance"
                               {:op (e/->string op)})))
        atoms (atom [])
        exprL (reify-side st op atoms L)
        exprR (reify-side st op atoms R)
        atomv @atoms
        ;; per-atom LawfulIdentity → marks neutral elements (so `norm` removes them).
        neutrals (mapv (fn [a]
                         (get-inst st env index "Std.LawfulIdentity" :identity carrier u op a))
                       atomv)
        neutral-idx (set (keep-indexed (fn [i n] (when n i)) neutrals))
        comm? (boolean (:comm pc))
        idem? (boolean (:idem pc))
        normL (norm-list (decode-toList exprL) neutral-idx comm? idem?)
        normR (norm-list (decode-toList exprR) neutral-idx comm? idem?)
        _ (when-not (= normL normR)
            (throw (ex-info "ac_rfl: the two sides are not AC-equal"
                            {:lhs (e/->string L) :rhs (e/->string R)})))
        ;; build the Context
        var-type (e/app* (C "Lean.Data.AC.Variable" [u]) carrier op)
        mk-var (fn [a inst]
                 (e/app* (C "Lean.Data.AC.Variable.mk" [u]) carrier op a
                         (opt-field (e/app* (C "Std.LawfulIdentity" [u]) carrier op a) inst)))
        vars-list (reduce (fn [acc i]
                            (e/app* (C "List.cons" [u]) var-type
                                    (mk-var (nth atomv i) (nth neutrals i)) acc))
                          (e/app (C "List.nil" [u]) var-type)
                          (range (dec (count atomv)) -1 -1))
        comm-field (opt-field (e/app* (C "Std.Commutative" [u]) carrier op) (:comm pc))
        idem-field (opt-field (e/app* (C "Std.IdempotentOp" [u]) carrier op) (:idem pc))
        arbitrary (first atomv)
        ctx (e/app* (C "Lean.Data.AC.Context.mk" [u]) carrier op (:assoc pc)
                    comm-field idem-field vars-list arbitrary)
        h-true (e/app* (C "Eq.refl" [one]) (C "Bool" []) (C "Bool.true" []))]
    (e/app* (C "Lean.Data.AC.Context.eq_of_norm" [u]) carrier ctx exprL exprR h-true)))

(defn ac-rfl
  "The `ac_rfl` tactic: close an associative(-commutative) equation goal by reflection normalization.
   Throws a tactic error if the goal is not an AC-provable equation."
  [ps]
  (basic/exact ps (ac-rfl-term ps)))
