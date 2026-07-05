;; Tactic layer — metavariable-aware, reduction-aware definitional equality.
;;
;; This is the analog of Lean 4's `Meta.isDefEq` (src/Lean/Meta/ExprDefEq.lean), which the
;; simp rewriter relies on (`Simp/Rewrite.lean` tryTheoremCore: `isDefEq lhs e`). It sits at the
;; tactic level, NOT the kernel: the kernel's `tc/is-def-eq` is reduction-based but has NO
;; metavariables, and the elaborator's `unify!` solves metavariables but does NOT reduce. This
;; namespace combines both — it solves metavariables AND reduces, so a named typeclass accessor
;; (`WSemiring.mul S inst`) unifies with the projection it unfolds to (`inst.1`).
;;
;; The public tactic API still accepts the historical fvar-backed `mctx` atom
;;   {mvar-id -> {:type Expr, :solution Expr|nil}, :levels {level-id -> Level}}
;; but `is-def-eq!` translates this into the Lean-shaped persistent metacontext in `ansatz.meta`,
;; runs the single meta implementation, and syncs successful assignments back.

(ns ansatz.tactic.unify
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta :as meta]))

;; ============================================================
;; Historical tactic metavariable context
;; ============================================================

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
   expr-fvar-mvar but still has an unsolved metavariable."
  [mctx e]
  (case (e/tag e)
    :fvar   (and (contains? @mctx (e/fvar-id e)) (nil? (solution mctx (e/fvar-id e))))
    ;; A real Expr.mvar node is not tracked by this legacy atom; report it as
    ;; unsolved so callers reject rather than record a term with an open hole.
    :mvar   true
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

;; ============================================================
;; Universe-level metavariables
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
;; Legacy tactic mctx <-> persistent meta mctx bridge
;; ============================================================

(defn- legacy-mvar-entry? [[id _]]
  (integer? id))

(defn- legacy-level->meta [l]
  (if-not (lvl/has-mvar? l)
    l
    (case (lvl/tag l)
      :succ (lvl/succ (legacy-level->meta (lvl/succ-pred l)))
      :max (lvl/level-max (legacy-level->meta (lvl/max-lhs l))
                           (legacy-level->meta (lvl/max-rhs l)))
      :imax (lvl/imax (legacy-level->meta (lvl/imax-lhs l))
                      (legacy-level->meta (lvl/imax-rhs l)))
      l)))

(declare legacy-expr->meta meta-expr->legacy)

(defn- legacy-expr->meta [legacy expr]
  (case (e/tag expr)
    :fvar (if (contains? legacy (e/fvar-id expr))
            (e/mvar (e/fvar-id expr))
            expr)
    :sort (e/sort' (legacy-level->meta (e/sort-level expr)))
    :const (e/const' (e/const-name expr) (mapv legacy-level->meta (e/const-levels expr)))
    :app (e/app (legacy-expr->meta legacy (e/app-fn expr))
                (legacy-expr->meta legacy (e/app-arg expr)))
    :lam (e/lam (e/lam-name expr)
                (legacy-expr->meta legacy (e/lam-type expr))
                (legacy-expr->meta legacy (e/lam-body expr))
                (e/lam-info expr))
    :forall (e/forall' (e/forall-name expr)
                       (legacy-expr->meta legacy (e/forall-type expr))
                       (legacy-expr->meta legacy (e/forall-body expr))
                       (e/forall-info expr))
    :let (e/let' (e/let-name expr)
                 (legacy-expr->meta legacy (e/let-type expr))
                 (legacy-expr->meta legacy (e/let-value expr))
                 (legacy-expr->meta legacy (e/let-body expr)))
    :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                  (legacy-expr->meta legacy (e/proj-struct expr)))
    :mdata (e/mdata (e/mdata-data expr)
                    (legacy-expr->meta legacy (e/mdata-expr expr)))
    expr))

(defn- meta-expr->legacy [legacy expr]
  (case (e/tag expr)
    :mvar (if (contains? legacy (e/mvar-id expr))
            (e/fvar (e/mvar-id expr))
            expr)
    :app (e/app (meta-expr->legacy legacy (e/app-fn expr))
                (meta-expr->legacy legacy (e/app-arg expr)))
    :lam (e/lam (e/lam-name expr)
                (meta-expr->legacy legacy (e/lam-type expr))
                (meta-expr->legacy legacy (e/lam-body expr))
                (e/lam-info expr))
    :forall (e/forall' (e/forall-name expr)
                       (meta-expr->legacy legacy (e/forall-type expr))
                       (meta-expr->legacy legacy (e/forall-body expr))
                       (e/forall-info expr))
    :let (e/let' (e/let-name expr)
                 (meta-expr->legacy legacy (e/let-type expr))
                 (meta-expr->legacy legacy (e/let-value expr))
                 (meta-expr->legacy legacy (e/let-body expr)))
    :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                  (meta-expr->legacy legacy (e/proj-struct expr)))
    :mdata (e/mdata (e/mdata-data expr)
                    (meta-expr->legacy legacy (e/mdata-expr expr)))
    expr))

(defn- legacy-lctx->meta [legacy lctx]
  (reduce-kv
   (fn [acc id decl]
     (assoc acc id
            (cond-> decl
              (:type decl) (update :type #(legacy-expr->meta legacy %))
              (:value decl) (update :value #(legacy-expr->meta legacy %)))))
   {}
   lctx))

(defn- meta-level-ids-in-expr [expr]
  (set (meta/unassigned-level-mvars meta/empty-context expr)))

(defn- build-meta-context [st legacy a b]
  (let [entries (filter legacy-mvar-entry? legacy)
        lctx-exprs (mapcat (fn [[_ {:keys [type value]}]] [type value])
                           (:lctx st))
        exprs (remove nil? (concat [a b]
                                   lctx-exprs
                                   (mapcat (fn [[_ {:keys [type solution]}]]
                                             [type solution])
                                           entries)))
        exprs (map #(legacy-expr->meta legacy %) exprs)
        level-ids (into (set (keys (:levels legacy)))
                        (mapcat meta-level-ids-in-expr exprs))
        lctx (legacy-lctx->meta legacy (:lctx st))]
    (-> (reduce meta/add-level-mvar-decl meta/empty-context level-ids)
        (as-> mctx
            (reduce (fn [mctx [id {:keys [type]}]]
                      (meta/add-expr-mvar-decl mctx id
                                               (legacy-expr->meta legacy type)
                                               lctx))
                    mctx entries))
        (as-> mctx
            (reduce (fn [mctx [id {:keys [solution]}]]
                      (if solution
                        (meta/assign-expr mctx id (legacy-expr->meta legacy solution))
                        mctx))
                    mctx entries))
        (as-> mctx
            (reduce (fn [mctx [id solution]]
                      (meta/assign-level mctx id solution))
                    mctx (:levels legacy))))))

(defn- sync-legacy-from-meta! [mctx meta-mctx]
  (let [legacy @mctx]
    (doseq [[id _] (filter legacy-mvar-entry? legacy)]
      (when-let [solution (meta/expr-assignment meta-mctx id)]
        (swap! mctx assoc-in [id :solution]
               (meta-expr->legacy legacy solution))))
    (doseq [[id solution] (:level-assignment meta-mctx)]
      (swap! mctx assoc-in [:levels id] solution))))

(defn- meta-is-def-eq!
  [st mctx bound a b]
  (let [legacy @mctx
        meta-mctx (build-meta-context st legacy a b)
        lctx (legacy-lctx->meta legacy (:lctx st))
        meta-st (tc/attach-lctx (tc/mk-tc-state (:env st)) lctx)
        a (legacy-expr->meta legacy a)
        b (legacy-expr->meta legacy b)]
    (when-let [meta-mctx (meta/is-def-eq meta-mctx meta-st bound a b)]
      (sync-legacy-from-meta! mctx meta-mctx)
      true)))

(defn is-def-eq!
  "Metavariable-aware, reduction-aware definitional equality.

   The public tactic API still accepts the historical fvar-backed `mctx` atom,
   but the implementation is the Lean-shaped persistent metacontext path from
   `ansatz.meta`; successful assignments are synced back into the tactic atom."
  ([st mctx a b]
   (is-def-eq! st mctx #{} a b))
  ([st mctx bound a b]
   (meta-is-def-eq! st mctx bound a b)))
