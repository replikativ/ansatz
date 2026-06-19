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
            [ansatz.prelude.algebra :as alg]
            [ansatz.prelude.ac :as ac]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (has? "wsum"))

(defn install!
  "Define `wsum` and the WSemiring big-operator laws into the current env (idempotent).
   Returns :installed. Assumes algebra classes are present (installs them if not)."
  []
  (alg/install-classes!)
  (ac/install!)
  (when-not (has? "wsum")
    (eval '(ansatz.core/defn wsum [S :- Type :implicit, m :- (WAddMonoid S), xs :- (List S)] S
             (match xs (List S) S
               (nil (WAddMonoid.zero m))
               (cons [hd tl] (WAddMonoid.add m hd (wsum m tl)))))))
  ;; Loop-invariant hoist (Mathlib List.sum_map_mul_left): a constant left-multiplier factors
  ;; out of a summed map.  ∑ (b * f x) = b * ∑ f x  over a (left-distributive) WSemiring.
  ;; Authored thinly — `(induction xs) <;> simp_all [wsum.eq_1 wsum.eq_2 …]` — riding wsum's
  ;; auto-generated constructor equations and the bundled WSemiring axioms applied to the
  ;; instance (`(WSemiring.mul_add m)`), exactly the way Lean's `simp [m.mul_add]` does.
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
  ;; Additivity of the big-operator: ∑ (f x + g x) = ∑ f x + ∑ g x, over a commutative monoid.
  ;; Mirrors Lean core's own style for List.sum lemmas — `List.sum_append` takes `Std.Associative` /
  ;; `Std.LawfulLeftIdentity` as instance args; here the commutative variant takes a `Std.Commutative
  ;; (WAddMonoid.add m)` hypothesis. The cons case is exactly the medial/interchange reshuffle
  ;; `(a+b)+(c+d) = (a+c)+(b+d)` (ac/op_medial), applied with op := the monoid add and the
  ;; `Std.Associative` instance DERIVED from the bundled `WAddMonoid.add_assoc m`. The keystone the
  ;; Fubini `wsum_map_sum_comm` (and thence the aggregate-level join reorder) is built on.
  (when-not (has? "wsum_map_add")
    (try
      (eval '(ansatz.core/theorem wsum_map_add
               [X :- Type, S :- Type, m :- (WAddMonoid S),
                hc :- (Std.Commutative S (WAddMonoid.add m)),
                f :- (=> X S), g :- (=> X S), xs :- (List X)]
               (= S
                  (wsum m (List.map X S (fn [x :- X] (WAddMonoid.add m (f x) (g x))) xs))
                  (WAddMonoid.add m (wsum m (List.map X S f xs)) (wsum m (List.map X S g xs))))
               (induction xs)
               (all_goals (simp_all [List.map_cons List.map_nil wsum.eq_1 wsum.eq_2
                                     (WAddMonoid.zero_add m) (WAddMonoid.add_zero m)]))
               (all_goals (try (rw (op_medial S (WAddMonoid.add m)
                                     (Std.Associative.mk S (WAddMonoid.add m) (WAddMonoid.add_assoc m)) hc
                                     (f head) (g head)
                                     (wsum m (List.map X S f tail)) (wsum m (List.map X S g tail))))))))
      (catch Throwable _ nil)))
  ;; ∑ (fun _ => 0) = 0 — the constant-zero map sum (Fubini's nil case needs it).
  (when-not (has? "wsum_map_const_zero")
    (try
      (eval '(ansatz.core/theorem wsum_map_const_zero
               [Y :- Type, S :- Type, m :- (WAddMonoid S), ys :- (List Y)]
               (= S (wsum m (List.map Y S (fn [y :- Y] (WAddMonoid.zero m)) ys)) (WAddMonoid.zero m))
               (induction ys)
               (all_goals (simp_all [List.map_cons List.map_nil wsum.eq_1 wsum.eq_2
                                     (WAddMonoid.zero_add m)]))))
      (catch Throwable _ nil)))
  ;; Fubini / nested-sum interchange (lean-wandler Laws/Frame.lean `sum_map_sum_comm`):
  ;;   ∑ₓ ∑ᵧ g x y = ∑ᵧ ∑ₓ g x y   over a commutative monoid.
  ;; The cons case applies `wsum_map_add` (the additivity keystone) to the transposed inner sum; simp
  ;; rewrites under the `λy` binder natively (no SOAC-congruence needed) and the nil case folds via
  ;; `wsum_map_const_zero`. THIS is the law the aggregate-level join reorder (which retires the
  ;; List.Perm cluster) is built on — the verified Fubini that makes join commutativity algebraic.
  (when-not (has? "wsum_map_sum_comm")
    (try
      (eval '(ansatz.core/theorem wsum_map_sum_comm
               [X :- Type, Y :- Type, S :- Type, m :- (WAddMonoid S),
                hc :- (Std.Commutative S (WAddMonoid.add m)), g :- (=> X (=> Y S)),
                xs :- (List X), ys :- (List Y)]
               (= S
                  (wsum m (List.map X S (fn [x :- X] (wsum m (List.map Y S (g x) ys))) xs))
                  (wsum m (List.map Y S (fn [y :- Y] (wsum m (List.map X S (fn [x :- X] (g x y)) xs))) ys)))
               (induction xs)
               (all_goals (simp_all [List.map_cons List.map_nil wsum.eq_1 wsum.eq_2
                                     (WAddMonoid.zero_add m) wsum_map_const_zero]))
               (all_goals (try (rw (wsum_map_add Y S m hc (g head)
                                     (fn [y :- Y] (wsum m (List.map X S (fn [x2 :- X] (g x2 y)) tail))) ys))))))
      (catch Throwable _ nil)))
  ;; ∑ (l1 ++ l2) = ∑ l1 + ∑ l2 — the monoid homomorphism on append (only associativity needed, no
  ;; commutativity). Stated over `HAppend.hAppend` (the spelling `List.flatMap_cons` produces) so it
  ;; fires as a simp lemma on flatMap results. cons case = one `add_assoc` rewrite.
  (when-not (has? "wsum_append")
    (try
      (eval '(ansatz.core/theorem wsum_append
               [S :- Type, m :- (WAddMonoid S), l1 :- (List S), l2 :- (List S)]
               (= S (wsum m (HAppend.hAppend (List S) (List S) (List S)
                                             (instHAppendOfAppend (List S) (List.instAppend S)) l1 l2))
                    (WAddMonoid.add m (wsum m l1) (wsum m l2)))
               (induction l1)
               (all_goals (simp_all [List.cons_append List.nil_append wsum.eq_1 wsum.eq_2
                                     (WAddMonoid.zero_add m)]))
               (all_goals (try (rw (WAddMonoid.add_assoc m head (wsum m tail) (wsum m l2)))))))
      (catch Throwable _ nil)))
  ;; ∑ (flatMap f l) = ∑ (map (fun x => ∑ (f x)) l) — the sum distributes over flatMap (lean-wandler's
  ;; `sum_flatMap`). cons case folds via `wsum_append` on the flatMap_cons append. The bridge from a
  ;; join (a flatMap) to its per-row aggregate — the core of `aggJoin_split`.
  (when-not (has? "wsum_flatMap")
    (try
      (eval '(ansatz.core/theorem wsum_flatMap
               [X :- Type, S :- Type, m :- (WAddMonoid S), f :- (=> X (List S)), l :- (List X)]
               (= S (wsum m (List.flatMap X S f l))
                    (wsum m (List.map X S (fn [x :- X] (wsum m (f x))) l)))
               (induction l)
               (all_goals (simp_all [List.flatMap_cons List.flatMap_nil List.map_cons List.map_nil
                                     wsum.eq_1 wsum.eq_2 wsum_append]))))
      (catch Throwable _ nil)))
  ;; ∑ (flatten LL) = ∑ (map ∑ LL) — sum over a list-of-lists. Needed because simp unfolds
  ;; `map h (flatMap g)` to `flatten (map …)` rather than keeping the `flatMap` head, so the
  ;; flatten-keyed form is what fires downstream (aggJoin_split).
  (when-not (has? "wsum_flatten")
    (try
      (eval '(ansatz.core/theorem wsum_flatten
               [S :- Type, m :- (WAddMonoid S), LL :- (List (List S))]
               (= S (wsum m (List.flatten S LL))
                    (wsum m (List.map (List S) S (fn [l :- (List S)] (wsum m l)) LL)))
               (induction LL)
               (all_goals (simp_all [List.flatten_cons List.flatten_nil List.map_cons List.map_nil
                                     wsum.eq_1 wsum.eq_2 wsum_append]))))
      (catch Throwable _ nil)))
  ;; aggJoin_split — THE FAQ factorization (lean-wandler Laws/Frame.lean `aggJoin_split`): the aggregate
  ;; of a join is the per-left-row sum over that row's matching bucket — i.e. O(|xs|·|ys|) → O(|xs|+|ys|)
  ;; via a pre-aggregated index. Join inlined (flatMap x → map (x,·) over the filtered ys); aggregated by
  ;; an abstract `h : (X×Y) → S`. PURE SIMP (map_flatMap → map_map → wsum_flatten → comp) — no induction,
  ;; no case-split. The core planner win; the join-REORDER (swap sides) additionally needs a filter→guard
  ;; lemma + Fubini. (`p : X→Y→Bool` is the match predicate; kf/lf/DecidableEq specialization later.)
  (when-not (has? "aggJoin_split")
    (try
      (eval '(ansatz.core/theorem aggJoin_split
               [X :- Type, Y :- Type, S :- Type, m :- (WAddMonoid S),
                p :- (=> X (=> Y Bool)), h :- (=> (Prod X Y) S), xs :- (List X), ys :- (List Y)]
               (= S
                  (wsum m (List.map (Prod X Y) S h
                            (List.flatMap X (Prod X Y)
                              (fn [x :- X] (List.map Y (Prod X Y) (fn [y :- Y] (Prod.mk x y))
                                            (List.filter Y (p x) ys))) xs)))
                  (wsum m (List.map X S (fn [x :- X]
                            (wsum m (List.map Y S (fn [y :- Y] (h (Prod.mk x y)))
                                      (List.filter Y (p x) ys)))) xs)))
               (simp [List.map_flatMap List.map_map wsum_flatten Function.comp_def])))
      (catch Throwable _ nil)))
  :installed)
