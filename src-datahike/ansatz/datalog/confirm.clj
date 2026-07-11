;; Direction-2 kernel foreign functions for datahike clauses: CONFIRM that a
;; recalled lemma actually applies to a goal by kernel definitional equality.
;;
;; Two flavors (we experiment with both):
;;   applies?    — a pure PREDICATE (fork the metacontext, defeq, return bool).
;;                 rel re-runs the unification for the winner.
;;   apply-lemma — mctx-IN → mctx-OUT: returns the forked+unified metacontext
;;                 as a per-row VALUE (nil = doesn't apply, which datahike drops).
;;                 rel adopts the winner's mctx directly — no recomputation.
;;                 The metacontext is a persistent value, so carrying it through
;;                 the query relation is clean and pure (no shared mutation).
(ns ansatz.datalog.confirm
  (:require [ansatz.rel :as r]
            [ansatz.meta :as meta]))

(defn lemma-out-mctx
  "Fork a rel state at `mctx`, make a goal mvar of type `goal-type`, and apply
   lemma `lemma-name` (peel its ∀-telescope, unify the conclusion with the goal
   by kernel is-def-eq). Returns the resulting metacontext if the lemma APPLIES
   (conclusion unifies; obligations remain as fresh holes), else nil.

   This is exactly `applyo`'s applicability check — reused, so the datalog
   confirmation and the rel search agree by construction."
  [env mctx goal-type lemma-name]
  (let [s0 (r/state env :mctx (or mctx meta/empty-context))
        res (r/run 1 s0
                   (r/fresh goal-type
                            (fn [g] (r/applyo g lemma-name (fn [_] r/succeed)))))]
    (when-let [s (first res)]
      (:mctx s))))

;; expensive (kernel defeq) → the planner places these AFTER the disc-tree
;; structural narrowing, so they run only on the handful of survivors.
(defn ^{:datahike/cost (fn [_ctx] 5000)}
  apply-lemma
  "mctx-threading confirmation: goal + lemma → the unified metacontext, or nil."
  [env mctx goal-type lemma-name]
  (lemma-out-mctx env mctx goal-type lemma-name))

(defn ^{:datahike/cost (fn [_ctx] 5000)}
  applies?
  "Pure-predicate confirmation: does the lemma apply to the goal? (bool)."
  [env mctx goal-type lemma-name]
  (some? (lemma-out-mctx env mctx goal-type lemma-name)))
