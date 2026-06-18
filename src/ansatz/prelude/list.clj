(ns ansatz.prelude.list
  "The list big-operator layer of the owned prelude: a polymorphic `wsum` (fold over a WAddMonoid)
   plus the semiring big-operator laws the FAQ frame rule cites — proved over WSemiring, the way
   lean-wandler's Laws/Frame.lean cites Mathlib's `List.sum_map_mul_left`/`_right`.

   `wsum` is authored at Lean's level of concision: a polymorphic structurally-recursive a/defn
       wsum {S} (m : WAddMonoid S) : List S → S
         | []      => m.zero
         | x :: xs => m.add x (wsum m xs)
   which auto-generates the constructor-keyed equation lemmas (wsum.eq_1/eq_2) that simp consumes.
   The laws are then `(induction xs) <;> simp [...]` — the bundled axioms (WSemiring.mul_add m …)
   applied to the instance and fed to simp, exactly Lean's `simp [m.mul_add]`.

   Requires the algebra classes installed (ansatz.prelude.algebra/install-classes!) and an env with
   the List equation lemmas (full Init store)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.prelude.algebra :as alg]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (has? "wsum"))

(defn install!
  "Define `wsum` and the WSemiring big-operator laws into the current env (idempotent).
   Returns :installed. Assumes algebra classes are present (installs them if not)."
  []
  (alg/install-classes!)
  (when-not (has? "wsum")
    (eval '(ansatz.core/defn wsum [S :- Type :implicit, m :- (WAddMonoid S), xs :- (List S)] S
             (match xs (List S) S
               (nil (WAddMonoid.zero m))
               (cons [hd tl] (WAddMonoid.add m hd (wsum m tl)))))))
  ;; Loop-invariant hoist (Mathlib List.sum_map_mul_left): a constant left-multiplier factors
  ;; out of a summed map.  ∑ (b * f x) = b * ∑ f x  over a (left-distributive) WSemiring.
  ;; NOTE: proving this thinly via `(induction xs) <;> simp [wsum …]` needs wsum's
  ;; constructor-keyed equation lemmas; auto-generation of those for a polymorphic+instance
  ;; def still has an fvar-leak in the eq-compiler (task #142 follow-on). Attempt it; on failure
  ;; leave wsum installed and usable (the law is wired once the eq-gen lands).
  (when-not (has? "wsum_map_mul_left")
    (try
      (eval '(ansatz.core/theorem wsum_map_mul_left
               [S :- Type :implicit, m :- (WSemiring S), b :- S, f :- (=> S S), xs :- (List S)]
               (= S
                  (wsum (WSemiring.toWAddMonoid m)
                        (List.map (fn [x :- S] (WSemiring.mul m b (f x))) xs))
                  (WSemiring.mul m b (wsum (WSemiring.toWAddMonoid m) (List.map f xs))))
               (induction xs)
               (all_goals (simp_all [wsum.eq_1 wsum.eq_2 List.map_nil List.map_cons
                                     (WSemiring.mul_zero m) (WSemiring.mul_add m)]))))
      (catch Throwable _ nil)))
  :installed)
