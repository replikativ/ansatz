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

(defn- has-mvar?
  "Does `e` (assumed zonked) contain any UNSOLVED metavariable?"
  [mctx e]
  (and (e/has-fvar-flag e)
       (case (e/tag e)
         :fvar (and (contains? @mctx (e/fvar-id e)) (nil? (solution mctx (e/fvar-id e))))
         :app    (or (has-mvar? mctx (e/app-fn e)) (has-mvar? mctx (e/app-arg e)))
         :lam    (or (has-mvar? mctx (e/lam-type e)) (has-mvar? mctx (e/lam-body e)))
         :forall (or (has-mvar? mctx (e/forall-type e)) (has-mvar? mctx (e/forall-body e)))
         :let    (or (has-mvar? mctx (e/let-type e)) (has-mvar? mctx (e/let-value e)) (has-mvar? mctx (e/let-body e)))
         :proj   (has-mvar? mctx (e/proj-struct e))
         :mdata  (has-mvar? mctx (e/mdata-expr e))
         false)))

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
;; isDefEq with metavariable assignment + reduction
;; ============================================================

(defn- whnf* [st e]
  (try (#'tc/cached-whnf st e) (catch Exception _ e)))

(declare is-def-eq!)

(defn- assign-or-recurse [st mctx a b]
  ;; a, b assumed zonked. Try mvar-assignment, else structural recursion.
  (cond
    (and (mvar? mctx a) (nil? (solution mctx (e/fvar-id a)))) (assign! mctx (e/fvar-id a) b)
    (and (mvar? mctx b) (nil? (solution mctx (e/fvar-id b)))) (assign! mctx (e/fvar-id b) a)
    ;; no metavariables either side → kernel's reduction-based defeq (robust)
    (and (not (has-mvar? mctx a)) (not (has-mvar? mctx b))) (tc/is-def-eq st a b)
    (= (e/tag a) (e/tag b))
    (case (e/tag a)
      :app    (and (is-def-eq! st mctx (e/app-fn a) (e/app-fn b))
                   (is-def-eq! st mctx (e/app-arg a) (e/app-arg b)))
      :const  (and (= (e/const-name a) (e/const-name b))
                   (= (count (e/const-levels a)) (count (e/const-levels b)))
                   (every? true? (map lvl/level= (e/const-levels a) (e/const-levels b))))
      :proj   (and (= (e/proj-type-name a) (e/proj-type-name b))
                   (= (e/proj-idx a) (e/proj-idx b))
                   (is-def-eq! st mctx (e/proj-struct a) (e/proj-struct b)))
      :lam    (and (is-def-eq! st mctx (e/lam-type a) (e/lam-type b))
                   (is-def-eq! st mctx (e/lam-body a) (e/lam-body b)))
      :forall (and (is-def-eq! st mctx (e/forall-type a) (e/forall-type b))
                   (is-def-eq! st mctx (e/forall-body a) (e/forall-body b)))
      :sort   (lvl/level= (e/sort-level a) (e/sort-level b))
      :fvar   (= (e/fvar-id a) (e/fvar-id b))
      (:lit-nat :lit-str :bvar) (= a b)
      false)
    :else false))

(defn is-def-eq!
  "Metavariable-aware, reduction-aware definitional equality (Lean's `Meta.isDefEq`).
   Solves metavariables of `mctx` in place; returns true on success.

   Strategy (mirrors `tc/is-def-eq*` plus metavariable cases):
   1. zonk both sides;
   2. syntactically equal → done;
   3. a bare unsolved metavariable → assign it (first-order);
   4. neither side has metavariables → delegate to the kernel's reduction-based `tc/is-def-eq`
      (handles all spelling differences via whnf, plus eta / proof-irrelevance);
   5. otherwise reduce both sides to whnf and recurse structurally, assigning metavariables at the
      positions they reach.

   `st` is a `tc/mk-tc-state` (with the goal's lctx attached); `mctx` is the metavariable atom."
  [st mctx a b]
  (let [a (zonk mctx a) b (zonk mctx b)]
    (or (= a b)
        (assign-or-recurse st mctx a b)
        ;; structural attempt failed without reducing — reduce to whnf and retry once
        (let [a' (whnf* st a) b' (whnf* st b)]
          (when (or (not (identical? a' a)) (not (identical? b' b)))
            (assign-or-recurse st mctx (zonk mctx a') (zonk mctx b')))))))
