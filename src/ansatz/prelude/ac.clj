(ns ansatz.prelude.ac
  "Associative-commutative reshuffles over a generic operator — the owned 'abel-lite' fragment.

   ansatz has no `ac_rfl` (and we deliberately don't port Lean's reflected `Lean.Meta.AC` normalizer:
   ~347 LOC of `Data.AC.Expr` machinery for a 2-shape need). Instead we mirror Lean core's OWN style
   for monoid lemmas — `List.sum_append` is proved `simp_all [Std.Associative.assoc,
   Std.LawfulLeftIdentity.left_id]`, and `Nat.add_add_add_comm` is literally
   `rw [add_assoc, add_assoc, add_left_comm b]`. We prove the two reshuffles ONCE, generically over any
   `op` carrying `[Std.Associative op]` + `[Std.Commutative op]`, via controlled `rewrite` chains using
   the Init accessors `Std.Associative.assoc` / `Std.Commutative.comm` (no Mathlib). They are the only
   AC shapes the aggregation big-operator laws (`wsum_map_add`, the Fubini `wsum_map_sum_comm`) need:

       op_left_comm  : op a (op b c)        = op b (op a c)
       op_medial     : op (op a b) (op c d) = op (op a c) (op b d)   -- the interchange / medial law

   `op` is abstract (an fvar), so these can't be disc-tree-keyed simp lemmas — they are applied
   EXPLICITLY (`rewrite`/`exact`) in the sum-law proofs, with `op` instantiated to the monoid's add.
   Each is `check-constant`-verified by `install!`. Requires the full Init store (the Std classes +
   accessors are present there). Companion: ansatz/docs/WANDLER_REIMPL_PLAN.md (Pillar B)."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn installed? [] (and (has? "op_left_comm") (has? "op_medial")))

(defn install!
  "Prove + register `op_left_comm` and `op_medial` into the current env (idempotent). Requires the
   full Init store (Std.Associative/Commutative + accessors). Returns :installed."
  []
  (when-not (has? "op_left_comm")
    (eval '(ansatz.core/theorem op_left_comm
                                [A :- Type, op :- (=> A (=> A A)),
                                 hassoc :- (Std.Associative A op), hcomm :- (Std.Commutative A op),
                                 a :- A, b :- A, c :- A]
                                (= A (op a (op b c)) (op b (op a c)))
             ;; (ab)c ← a(bc) ; swap inner a b ; (ba)c → b(ac) ; the last `rw` auto-closes by rfl
                                (rw <- (Std.Associative.assoc A op hassoc a b c))
                                (rw (Std.Commutative.comm A op hcomm a b))
                                (rw (Std.Associative.assoc A op hassoc b a c)))))
  (when-not (has? "op_medial")
    (eval '(ansatz.core/theorem op_medial
                                [A :- Type, op :- (=> A (=> A A)),
                                 hassoc :- (Std.Associative A op), hcomm :- (Std.Commutative A op),
                                 a :- A, b :- A, c :- A, d :- A]
                                (= A (op (op a b) (op c d)) (op (op a c) (op b d)))
             ;; (ab)(cd) → a(b(cd)) → a((bc)d) → a((cb)d) → a(c(bd)) → (ac)(bd); last `rw` auto-closes
                                (rw (Std.Associative.assoc A op hassoc a b (op c d)))
                                (rw <- (Std.Associative.assoc A op hassoc b c d))
                                (rw (Std.Commutative.comm A op hcomm b c))
                                (rw (Std.Associative.assoc A op hassoc c b d))
                                (rw <- (Std.Associative.assoc A op hassoc a c (op b d))))))
  :installed)
