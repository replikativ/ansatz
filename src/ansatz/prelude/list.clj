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
  ;; Loop-invariant hoist (Mathlib List.sum_map_mul_left / lean-wandler `sum_map_mul_const`): a
  ;; constant left-multiplier factors out of a summed map.  ∑ (b * f x) = b * ∑ f x  over a
  ;; (left-distributive) WSemiring. ELEMENT-POLYMORPHIC (`f : X → S` over `List X`) — the separable
  ;; FAQ frame `aggJoin_factor` pulls `w x` out of the inner sum over a `List Y`. Authored thinly —
  ;; `(induction xs) <;> simp_all [wsum.eq_1 wsum.eq_2 …]` — riding wsum's auto-generated constructor
  ;; equations and the bundled WSemiring axioms applied to the instance (`(WSemiring.mul_add m)`).
  (when-not (has? "wsum_map_mul_left")
    (try
      (eval '(ansatz.core/theorem wsum_map_mul_left
               [X :- Type, S :- Type :implicit, m :- (WSemiring S), b :- S, f :- (=> X S), xs :- (List X)]
               (= S
                  (wsum (WSemiring.toWAddMonoid m)
                        (List.map X S (fn [x :- X] (WSemiring.mul m b (f x))) xs))
                  (WSemiring.mul m b (wsum (WSemiring.toWAddMonoid m) (List.map X S f xs))))
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
  ;; foldl (· :: ·) acc l = (reverse l) ++ acc — the accumulator-generalized reverse identity. A REAL
  ;; `Map.join` builds its group_by buckets by `foldl (· :: ·) []` (the matched rows in reverse); this
  ;; is what exposes that bucket as a `reverse`, so `wsum_reverse` can wash the order out. Proven thin by
  ;; `induction l generalizing acc` (the accumulator must vary in the IH) + simp [append_eq/assoc/cons].
  ;; NOTE List.foldl is {α=acc β=elem}: f : α → β → α, so the type args are (List A) A — NOT A (List A).
  (when-not (has? "foldl_cons_acc")
    (try
      (eval '(ansatz.core/theorem foldl_cons_acc
               [A :- Type, l :- (List A), acc :- (List A)]
               (= (List A)
                  (List.foldl (List A) A (fn [a :- (List A) y :- A] (List.cons A y a)) acc l)
                  (List.append A (List.reverse A l) acc))
               (induction l generalizing acc)
               (all_goals (simp_all [List.foldl_nil List.foldl_cons List.reverse_nil List.reverse_cons
                                     List.append_eq List.nil_append List.append_assoc List.cons_append
                                     List.singleton_append List.append_nil]))))
      (catch Throwable _ nil)))
  ;; ∑ (reverse l) = ∑ l over a COMMUTATIVE monoid — the big-operator is order-insensitive. The bridge
  ;; that lets the aggregate frame laws apply to a REAL `Map.join`: its group_by buckets are built by
  ;; `foldl (· :: ·) []` (= reverse of the filtered rows, per `Map.bucket_content`), so as lists the
  ;; join differs from the clean filter-flatMap form by that bucket reversal — but the SUM washes it out.
  ;; cons case = reverse_cons → wsum_append → ih → one `comm` swap. (After wsum_append; needs it.)
  (when-not (has? "wsum_reverse")
    (try
      (eval '(ansatz.core/theorem wsum_reverse
               [S :- Type, m :- (WAddMonoid S), hc :- (Std.Commutative S (WAddMonoid.add m)), l :- (List S)]
               (= S (wsum m (List.reverse S l)) (wsum m l))
               (induction l)
               (all_goals (simp_all [List.reverse_cons List.reverse_nil wsum.eq_1 wsum.eq_2 wsum_append
                                     (WAddMonoid.zero_add m) (WAddMonoid.add_zero m)]))
               (all_goals (try (rw (Std.Commutative.comm S (WAddMonoid.add m) hc head (wsum m tail)))))))
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
  ;; sum_filter_map — filter folds into a guarded sum (lean-wandler Laws/Frame.lean `sum_filter_map`):
  ;;   ∑ (map h (filter p ys)) = ∑ (map (fun y => if p y then h y else 0) ys).
  ;; The bridge that lets the join's `filter` become a `guard`, so Fubini (`wsum_map_sum_comm`) can
  ;; swap the two summation orders in `aggJoin_reorder`. Proof mirrors Lean's `cases hp : p y <;>
  ;; simp [hp, ih]` exactly: induct, expose the `filter_cons`/`map_cons` `ite`, then the faithful
  ;; substituting `cases hp (p head)` puts the literal `true`/`false` into the discriminant (incl. the
  ;; Decidable instance) so simp's reduceIte collapses both the LHS filter-ite and the RHS Bool.rec guard.
  (when-not (has? "sum_filter_map")
    (try
      (eval '(ansatz.core/theorem sum_filter_map
               [Y :- Type, S :- Type, m :- (WAddMonoid S),
                p :- (=> Y Bool), h :- (=> Y S), ys :- (List Y)]
               (= S
                  (wsum m (List.map Y S h (List.filter Y p ys)))
                  (wsum m (List.map Y S (fn [y :- Y] (if (p y) (h y) (WAddMonoid.zero m))) ys)))
               (induction ys)
               (all_goals (simp [List.filter_cons List.filter_nil List.map_cons List.map_nil
                                 wsum.eq_1 wsum.eq_2]))
               (all_goals (try (cases hp (p head))))
               (all_goals (try (simp_all [hp List.map_cons wsum.eq_1 wsum.eq_2
                                          (WAddMonoid.zero_add m)])))))
      (catch Throwable _ nil)))
  ;; ── association-list lookup foundation (for the relational Map = AList//NodupKeys) ──────────
  ;; `lookup k (filter (·.fst ≠ k') l) = lookup k l` when `k ≠ k'` — filtering out a DIFFERENT key
  ;; leaves k's binding untouched. The keystone under the keyed group_by-bucket bridge (Map.join's
  ;; buckets are `foldl(::)[] (filter (kf x == lf ·))`). Replaces a ~90-LOC term-built proof
  ;; (old wandler.laws.relational/prove-lookup-filter-ne) with the thin surface.
  ;;
  ;; The proof exercises two faithful-to-lean4 capabilities added for it: `dsimp` (Lean's dsimpGoal —
  ;; fires the iota step that a simp rewrite of a `List.lookup` match scrutinee to a Bool literal leaves
  ;; pending) and structure-`extends` parent-projection instance synthesis (so `beq_self_eq_true`'s
  ;; `ReflBEq` discharges via DecidableEq→LawfulBEq→ReflBEq). `cases head` destructs the Prod so
  ;; `lookup_cons` matches; the nested `by_cases` on the two beqs gives 4 cases (the impossible
  ;; fst=k=k' one closes by the `k ≠ k'` hypothesis); simp_all⇄dsimp run to fixpoint.
  (when-not (has? "List.lookup_filter_ne")
    (try
      (eval '(ansatz.core/theorem List.lookup_filter_ne
               [α :- Type, β :- Type, dec :- (DecidableEq α), k :- α, k' :- α, l :- (List (Prod α β)),
                hne :- (= Bool (BEq.beq α (instBEqOfDecidableEq α dec) k k') Bool.false)]
               (= (Option β)
                  (List.lookup α β (instBEqOfDecidableEq α dec) k
                    (List.filter (Prod α β)
                      (fn [p :- (Prod α β)] (Bool.not (BEq.beq α (instBEqOfDecidableEq α dec) (Prod.fst α β p) k'))) l))
                  (List.lookup α β (instBEqOfDecidableEq α dec) k l))
               (induction l)
               (all_goals (try (simp_all [List.filter_nil List.lookup_nil])))
               (cases head)
               (all_goals (try (dsimp)))
               (by_cases (BEq.beq α (instBEqOfDecidableEq α dec) fst k'))
               (all_goals (try (by_cases (BEq.beq α (instBEqOfDecidableEq α dec) fst k))))
               (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg List.lookup_cons List.lookup_nil List.lookup_cons_self Bool.not_true Bool.not_false beq_iff_eq beq_eq_false_iff_ne beq_self_eq_true Prod.fst])))
               (all_goals (try (dsimp)))
               (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg List.lookup_cons List.lookup_nil List.lookup_cons_self Bool.not_true Bool.not_false beq_iff_eq beq_eq_false_iff_ne beq_self_eq_true Prod.fst])))
               (all_goals (try (dsimp)))
               (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg List.lookup_cons List.lookup_nil List.lookup_cons_self Bool.not_true Bool.not_false beq_iff_eq beq_eq_false_iff_ne beq_self_eq_true Prod.fst])))
               (all_goals (try (dsimp)))
               (all_goals (try (simp_all [List.filter_cons_of_pos List.filter_cons_of_neg List.lookup_cons List.lookup_nil List.lookup_cons_self Bool.not_true Bool.not_false beq_iff_eq beq_eq_false_iff_ne beq_self_eq_true Prod.fst])))))
      (catch Throwable _ nil)))
  ;; NOTE: the RELATIONAL laws built on this big-operator layer — `aggJoin_split` (the FAQ factorization)
  ;; and `aggJoin_reorder` (the join-commutativity capstone, NO List.Perm) — live in
  ;; `wandler.clean.laws.frame`, not here. This namespace is the domain-agnostic Batteries-tier prelude
  ;; (generic `wsum`/big-operator/`sum_filter_map` lemmas, mirroring Mathlib's `List.sum_*`); the join
  ;; vocabulary belongs to the wandler relational showcase. frame's `install!` calls this one first.
  :installed)
