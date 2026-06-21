;; Tactic layer — metavariable-aware, reduction-aware definitional equality.
;;
;; This is the analog of Lean 4's `Meta.isDefEq` (src/Lean/Meta/ExprDefEq.lean), which the
;; simp rewriter relies on (`Simp/Rewrite.lean` tryTheoremCore: `isDefEq lhs e`). It sits at the
;; tactic level, NOT the kernel: the kernel's `tc/is-def-eq` is reduction-based but has NO
;; metavariables, and the elaborator's `unify!` solves metavariables but does NOT reduce. This
;; namespace combines both — it solves metavariables AND reduces, so a named typeclass accessor
;; (`WSemiring.mul S inst`) unifies with the projection it unfolds to (`inst.1`).
;;
;; Metavariables are represented as fvars whose id is registered in an `mctx` atom
;;   {mvar-id → {:type Expr, :solution Expr|nil}}
;; (the same fvars-as-metavars convention the elaborator uses). The kernel stays pure: for any
;; sub-problem with no metavariables on either side we delegate straight to `tc/is-def-eq`, reusing
;; its robust reduction (smart-unfolding, eta, proof irrelevance).

(ns ansatz.tactic.unify
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.level :as lvl]))

;; ============================================================
;; Metavariable context
;; ============================================================

(defn mvar?
  "Is `e` a metavariable fvar registered in `mctx`?"
  [mctx e]
  (and (e/fvar? e) (contains? @mctx (e/fvar-id e))))

(defn- solution [mctx id] (get-in @mctx [id :solution]))

(defn fresh-mvar!
  "Register a fresh metavariable of the given type; return it as an fvar Expr.
   `id` must be unique (caller supplies it, e.g. from the proof state's next-id)."
  [mctx id type]
  (swap! mctx assoc id {:type type :solution nil})
  (e/fvar id))

(defn zonk
  "Lean's `instantiateMVars`: replace solved metavariables by their solutions (chasing chains)."
  [mctx e]
  (if-not (e/has-fvar-flag e)
    e
    (case (e/tag e)
      :fvar (if (contains? @mctx (e/fvar-id e))
              (if-let [s (solution mctx (e/fvar-id e))]
                (zonk mctx s)
                e)
              e)
      :app    (e/app (zonk mctx (e/app-fn e)) (zonk mctx (e/app-arg e)))
      :lam    (e/lam (e/lam-name e) (zonk mctx (e/lam-type e)) (zonk mctx (e/lam-body e)) (e/lam-info e))
      :forall (e/forall' (e/forall-name e) (zonk mctx (e/forall-type e)) (zonk mctx (e/forall-body e)) (e/forall-info e))
      :let    (e/let' (e/let-name e) (zonk mctx (e/let-type e)) (zonk mctx (e/let-value e)) (zonk mctx (e/let-body e)))
      :proj   (e/proj (e/proj-type-name e) (e/proj-idx e) (zonk mctx (e/proj-struct e)))
      :mdata  (e/mdata (e/mdata-data e) (zonk mctx (e/mdata-expr e)))
      e)))

(declare zonk-level)

(defn- level-unsolved-mvar?
  "Does level `l` mention an unsolved level-mvar (after chasing solutions in `mctx`)?"
  [mctx l]
  (lvl/has-mvar? (zonk-level mctx l)))

(defn- has-mvar?
  "Does `e` (assumed zonked) contain any UNSOLVED metavariable — EXPR-mvar (faked fvar) OR LEVEL-mvar?
   Mirrors Lean's `Expr.hasMVar`, whose flag is set by both expr and level mvars. We can't rely on the
   fvar flag (level-mvars in const/sort levels don't set it), so we always traverse — apply/rewrite
   terms are small. Level-mvars are why this matters: an expr like `List.Perm.{?lm} …` carries NO
   expr-fvar-mvar but MUST NOT be treated as concrete, else `is-def-eq!` ships it to the kernel's
   level-blind `tc/is-def-eq` instead of recursing into `is-level-def-eq!`."
  [mctx e]
  (case (e/tag e)
    :fvar   (and (contains? @mctx (e/fvar-id e)) (nil? (solution mctx (e/fvar-id e))))
    :const  (boolean (some #(level-unsolved-mvar? mctx %) (e/const-levels e)))
    :sort   (level-unsolved-mvar? mctx (e/sort-level e))
    :app    (or (has-mvar? mctx (e/app-fn e)) (has-mvar? mctx (e/app-arg e)))
    :lam    (or (has-mvar? mctx (e/lam-type e)) (has-mvar? mctx (e/lam-body e)))
    :forall (or (has-mvar? mctx (e/forall-type e)) (has-mvar? mctx (e/forall-body e)))
    :let    (or (has-mvar? mctx (e/let-type e)) (has-mvar? mctx (e/let-value e)) (has-mvar? mctx (e/let-body e)))
    :proj   (has-mvar? mctx (e/proj-struct e))
    :mdata  (has-mvar? mctx (e/mdata-expr e))
    false))

(defn has-unassigned-mvars?
  "Public: does `e` still mention any unsolved metavariable after zonking?
   Lean's `hasAssignableMVar`, used to reject incomplete rewrite matches."
  [mctx e]
  (has-mvar? mctx (zonk mctx e)))

(defn- occurs?
  "Occurs check: does metavariable `id` appear in `e` (assumed zonked)?"
  [mctx id e]
  (and (e/has-fvar-flag e)
       (case (e/tag e)
         :fvar (= (e/fvar-id e) id)
         :app    (or (occurs? mctx id (e/app-fn e)) (occurs? mctx id (e/app-arg e)))
         :lam    (or (occurs? mctx id (e/lam-type e)) (occurs? mctx id (e/lam-body e)))
         :forall (or (occurs? mctx id (e/forall-type e)) (occurs? mctx id (e/forall-body e)))
         :let    (or (occurs? mctx id (e/let-type e)) (occurs? mctx id (e/let-value e)) (occurs? mctx id (e/let-body e)))
         :proj   (occurs? mctx id (e/proj-struct e))
         :mdata  (occurs? mctx id (e/mdata-expr e))
         false)))

(defn- assign!
  "Assign metavariable `id := v` (with occurs check). Returns true on success."
  [mctx id v]
  (when-not (occurs? mctx id v)
    (swap! mctx assoc-in [id :solution] v)
    true))

;; ============================================================
;; Universe-level metavariables (Lean's level isDefEq, LevelDefEq.lean)
;; ============================================================
;; Level-mvar solutions live in the SAME mctx atom under the `:levels` sub-map {lid → Level} (like
;; Lean's MetavarContext holding eAssignment + lAssignment together). Expr-mvar code keys mctx by int
;; fvar-id and never touches `:levels`, so the two coexist.

(defn zonk-level
  "instantiateLevelMVars: replace solved level-mvars by their solutions (chasing chains)."
  [mctx l]
  (if-not (lvl/has-mvar? l)
    l
    (case (lvl/tag l)
      :mvar (if-let [s (get-in @mctx [:levels (lvl/mvar-id l)])] (zonk-level mctx s) l)
      :succ (lvl/succ (zonk-level mctx (lvl/succ-pred l)))
      :max  (lvl/level-max (zonk-level mctx (lvl/max-lhs l)) (zonk-level mctx (lvl/max-rhs l)))
      :imax (lvl/imax (zonk-level mctx (lvl/imax-lhs l)) (zonk-level mctx (lvl/imax-rhs l)))
      l)))

(defn is-level-def-eq!
  "Lean's `isLevelDefEqAux` / `solve` (LevelDefEq.lean:90-159): assign level-mvars in `mctx`'s `:levels`
   table during level unification. CONCRETE fast-path (neither side has a level-mvar) delegates to the
   existing robust `lvl/level=`, so behavior is UNCHANGED when no level-mvars are in play (regression-
   safe). Otherwise: structural recurse; mvar→assign with occurs check (mandatory, LevelDefEq.lean:100);
   zero-vs-max/imax decomposition. Defers the solveSelfMax/tryApproxMaxMax approximations (:37-75) —
   standalone univ-poly lemmas (Perm ctors etc.) never hit them."
  [mctx a b]
  (let [a (zonk-level mctx a) b (zonk-level mctx b)]
    (cond
      (and (not (lvl/has-mvar? a)) (not (lvl/has-mvar? b))) (lvl/level= a b)
      (lvl/level= a b) true
      (and (lvl/succ? a) (lvl/succ? b)) (is-level-def-eq! mctx (lvl/succ-pred a) (lvl/succ-pred b))
      (lvl/mvar? a) (when-not (lvl/occurs? (lvl/mvar-id a) b)
                      (swap! mctx assoc-in [:levels (lvl/mvar-id a)] b) true)
      (lvl/mvar? b) (when-not (lvl/occurs? (lvl/mvar-id b) a)
                      (swap! mctx assoc-in [:levels (lvl/mvar-id b)] a) true)
      (and (lvl/level-zero? a) (lvl/max? b))
      (boolean (and (is-level-def-eq! mctx a (lvl/max-lhs b)) (is-level-def-eq! mctx a (lvl/max-rhs b))))
      (and (lvl/max? a) (lvl/level-zero? b))
      (boolean (and (is-level-def-eq! mctx (lvl/max-lhs a) b) (is-level-def-eq! mctx (lvl/max-rhs a) b)))
      (and (lvl/level-zero? a) (lvl/imax? b)) (is-level-def-eq! mctx a (lvl/imax-rhs b))
      (and (lvl/imax? a) (lvl/level-zero? b)) (is-level-def-eq! mctx (lvl/imax-rhs a) b)
      :else false)))

(defn zonk-levels-in-expr
  "Instantiate solved level-mvars in every const/sort level of `e` (a separate pass from `zonk`, which
   only chases EXPR-mvars and short-circuits on the fvar flag). Used on a finished proof term before the
   trusted kernel check, which must see no level-mvar."
  [mctx e]
  (case (e/tag e)
    :const (e/const' (e/const-name e) (mapv #(zonk-level mctx %) (e/const-levels e)))
    :sort  (e/sort' (zonk-level mctx (e/sort-level e)))
    :app   (e/app (zonk-levels-in-expr mctx (e/app-fn e)) (zonk-levels-in-expr mctx (e/app-arg e)))
    :lam   (e/lam (e/lam-name e) (zonk-levels-in-expr mctx (e/lam-type e)) (zonk-levels-in-expr mctx (e/lam-body e)) (e/lam-info e))
    :forall (e/forall' (e/forall-name e) (zonk-levels-in-expr mctx (e/forall-type e)) (zonk-levels-in-expr mctx (e/forall-body e)) (e/forall-info e))
    :let   (e/let' (e/let-name e) (zonk-levels-in-expr mctx (e/let-type e)) (zonk-levels-in-expr mctx (e/let-value e)) (zonk-levels-in-expr mctx (e/let-body e)))
    :proj  (e/proj (e/proj-type-name e) (e/proj-idx e) (zonk-levels-in-expr mctx (e/proj-struct e)))
    :mdata (e/mdata (e/mdata-data e) (zonk-levels-in-expr mctx (e/mdata-expr e)))
    e))

;; ============================================================
;; isDefEq with metavariable assignment + reduction
;; ============================================================

(defn- whnf* [st e]
  (try (#'tc/cached-whnf st e) (catch Exception _ e)))

(declare is-def-eq!)

(defn- mvar-app-spine
  "If `e` is `(?m a1 … an)` with `?m` an unsolved metavariable (n ≥ 1), return [mvar-id [a1 … an]];
   else nil. (A bare mvar with n=0 is handled by direct assignment, not the pattern path.)"
  [mctx e]
  (when (e/app? e)
    (loop [h e, args ()]
      (cond
        (and (mvar? mctx h) (nil? (solution mctx (e/fvar-id h)))) [(e/fvar-id h) (vec args)]
        (e/app? h) (recur (e/app-fn h) (cons (e/app-arg h) args))
        :else nil))))

(defn- fvar-decl-type [st id]
  (when-let [d (red/lctx-lookup (:lctx st) id)] (:type d)))

(defn- try-pattern!
  "Lean's `processAssignment`/`checkAssignment` MILLER-PATTERN case (ExprDefEq.lean:1267): solve
   `?m x1 … xn := v` where the `xi` are DISTINCT fvars LOCAL to this unification (`bound` = the
   binder fvars opened while descending into λ/∀), by assigning `?m := λ x1 … xn. abstract(v,[xi])`
   (`mkLambdaFVars`). Faithful pattern condition: args are distinct bound fvars; occurs-check `?m∉v`;
   binder types must be known. Returns true on assignment, nil to fall through to the caller's
   first-order approximation (the structural `:app` decomposition) — exactly Lean's pattern→FOApprox
   order. SOUNDNESS rests on the kernel: a mis-typed lambda fails the final `check-constant`."
  [st mctx bound mvar-id args v]
  (when (and (every? (fn [a] (and (e/fvar? a) (contains? bound (e/fvar-id a)))) args)
             (let [ids (map e/fvar-id args)] (apply distinct? ids))
             (not (occurs? mctx mvar-id v)))
    (let [ids (mapv e/fvar-id args)
          types (mapv (fn [id] (fvar-decl-type st id)) ids)]
      (when (every? some? types)
        (let [body (e/abstract-many v ids)
              ;; build λ (x1:T1) … (xn:Tn). body, each Ti abstracted over the preceding args (Tn may
              ;; depend on x1…x_{n-1}). Wrap innermost-first.
              lam (reduce (fn [acc i]
                            (let [ti (e/abstract-many (zonk mctx (nth types i)) (subvec ids 0 i))]
                              (e/lam "x" ti acc :default)))
                          body
                          (reverse (range (count ids))))]
          (assign! mctx mvar-id lam))))))

(defn- open-binder
  "Open a λ/∀ binder for body comparison (mirrors the kernel `is-def-eq*` :lam/:forall): a fresh fvar
   with the domain type, recursing on the instantiated bodies with the fvar added to `bound`."
  [st mctx bound dom name body-a body-b]
  (let [fid (long (swap! (:next-id st) inc))
        fv (e/fvar fid)
        st' (update st :lctx red/lctx-add-local fid name (zonk mctx dom))]
    (is-def-eq! st' mctx (conj bound fid) (e/instantiate1 body-a fv) (e/instantiate1 body-b fv))))

(defn- assign-or-recurse [st mctx bound a b]
  ;; a, b assumed zonked. Try mvar-assignment / pattern-solve, else structural recursion.
  (cond
    (and (mvar? mctx a) (nil? (solution mctx (e/fvar-id a)))) (assign! mctx (e/fvar-id a) b)
    (and (mvar? mctx b) (nil? (solution mctx (e/fvar-id b)))) (assign! mctx (e/fvar-id b) a)
    ;; no metavariables either side → kernel's reduction-based defeq (robust)
    (and (not (has-mvar? mctx a)) (not (has-mvar? mctx b))) (tc/is-def-eq st a b)
    :else
    (or
      ;; Miller pattern: `?m x1…xn =?= v` (both orientations), tried BEFORE first-order decomposition.
     (when-let [[mid args] (mvar-app-spine mctx a)] (try-pattern! st mctx bound mid args b))
     (when-let [[mid args] (mvar-app-spine mctx b)] (try-pattern! st mctx bound mid args a))
      ;; first-order approximation / structural recursion
     (when (= (e/tag a) (e/tag b))
       (case (e/tag a)
         :app    (and (is-def-eq! st mctx bound (e/app-fn a) (e/app-fn b))
                      (is-def-eq! st mctx bound (e/app-arg a) (e/app-arg b)))
         :const  (and (= (e/const-name a) (e/const-name b))
                      (= (count (e/const-levels a)) (count (e/const-levels b)))
                      (every? true? (map #(is-level-def-eq! mctx %1 %2) (e/const-levels a) (e/const-levels b))))
         :proj   (and (= (e/proj-type-name a) (e/proj-type-name b))
                      (= (e/proj-idx a) (e/proj-idx b))
                      (is-def-eq! st mctx bound (e/proj-struct a) (e/proj-struct b)))
         :lam    (and (is-def-eq! st mctx bound (e/lam-type a) (e/lam-type b))
                      (open-binder st mctx bound (e/lam-type a) (e/lam-name a) (e/lam-body a) (e/lam-body b)))
         :forall (and (is-def-eq! st mctx bound (e/forall-type a) (e/forall-type b))
                      (open-binder st mctx bound (e/forall-type a) (e/forall-name a) (e/forall-body a) (e/forall-body b)))
         :sort   (is-level-def-eq! mctx (e/sort-level a) (e/sort-level b))
         :fvar   (= (e/fvar-id a) (e/fvar-id b))
         (:lit-nat :lit-str :bvar) (= a b)
         false)))))

(defn is-def-eq!
  "Metavariable-aware, reduction-aware definitional equality (Lean's `Meta.isDefEq`).
   Solves metavariables of `mctx` in place; returns true on success.

   Strategy (mirrors `tc/is-def-eq*` plus metavariable cases):
   1. zonk both sides;
   2. syntactically equal → done;
   3. a bare unsolved metavariable → assign it (first-order);
   4. neither side has metavariables → delegate to the kernel's reduction-based `tc/is-def-eq`
      (handles all spelling differences via whnf, plus eta / proof-irrelevance);
   5. the MILLER-PATTERN case `?m x1…xn =?= v` (xi distinct locally-bound fvars) → solve by
      `?m := λ x1…xn. abstract(v)` (Lean `processAssignment`); λ/∀ bodies are compared by OPENING the
      binder with a fresh fvar (Lean `isDefEqBinding`), so a function-metavar can never capture a
      loose bound variable;
   6. otherwise reduce both sides to whnf and recurse structurally, assigning metavariables at the
      positions they reach.

   `st` is a `tc/mk-tc-state` (with the goal's lctx attached); `mctx` is the metavariable atom.
   `bound` (4-arg arity defaults to ∅) is the set of fvar ids opened from binders during this run —
   the only fvars eligible as Miller-pattern arguments."
  ([st mctx a b] (is-def-eq! st mctx #{} a b))
  ([st mctx bound a b]
   ;; instantiateMVars = chase BOTH expr- and level-mvar solutions. The level pass only runs when some
   ;; level-mvar has been solved (regression-safe: zero cost when no level-mvars are in play), so a
   ;; solved level never reaches the kernel's level-blind `tc/is-def-eq` un-substituted.
   (let [inst (fn [e] (let [e (zonk mctx e)]
                        (if (seq (get @mctx :levels)) (zonk-levels-in-expr mctx e) e)))
         a (inst a) b (inst b)]
     (or (= a b)
         (assign-or-recurse st mctx bound a b)
         ;; structural attempt failed without reducing — reduce to whnf and retry once
         (let [a' (whnf* st a) b' (whnf* st b)]
           (when (or (not (identical? a' a)) (not (identical? b' b)))
             (assign-or-recurse st mctx bound (zonk mctx a') (zonk mctx b'))))))))
