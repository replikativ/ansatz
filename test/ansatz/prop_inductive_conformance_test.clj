(ns ansatz.prop-inductive-conformance-test
  "Direct translations of test/lean/prop_inductive_conformance.lean.
  Uses list-conformance-test translation rules; explicit type arguments spell Lean @ applications.
  Constructor branches use ansatz field names. No alternative proof scripts for gaps."
  (:require [clojure.test :refer [deftest]]
            [ansatz.conformance-support :as cs]))

;; Lean reference: src/Lean/Elab/Tactic/{Induction,Simp,Decide}.lean,
;; evalInductionCore/evalCasesCore, evalSimp, evalDecideCore.
(def ^:private defs
  '[(ansatz.core/inductive Mem [x Nat] :in Prop :indices [xs (List Nat)]
                           (head [t (List Nat)] :where [(cons x t)])
                           (tail [y Nat] [t (List Nat)] [h (Mem x t)] :where [(cons y t)]))
    (ansatz.core/inductive All [p (=> Nat Prop)] :in Prop :indices [xs (List Nat)]
                           (nil :where [(nil)])
                           (cons [x Nat] [xs (List Nat)] [hx (p x)] [ht (All p xs)] :where [(cons x xs)]))
    (ansatz.core/inductive Sorted [] :in Prop :indices [n Nat xs (List Nat)]
                           (nil [n Nat] :where [n (nil)])
                           (cons [n Nat] [x Nat] [xs (List Nat)] [hx (le n x)] [ht (Sorted x xs)] :where [n (cons x xs)]))
    (ansatz.core/inductive Reach [r (=> Nat Nat Prop)] :in Prop :indices [x Nat z Nat]
                           (refl [x Nat] :where [x x])
                           (step [x Nat] [y Nat] [z Nat] [hxy (r x y)] [hyz (Reach r y z)] :where [x z]))])

(def ^:private theorems
  '[[p01_mem_head [x :- Nat, xs :- (List Nat)]
     (Mem x (List.cons Nat x xs))
     [(constructor)]]
    [p02_mem_tail [x :- Nat, y :- Nat, xs :- (List Nat), h :- (Mem x xs)]
     (Mem x (List.cons Nat y xs))
     [(exact (Mem.tail x y xs h))]]
    [p03_mem_nil [x :- Nat, h :- (Mem x (List.nil Nat))]
     False
     [(cases h)]]
    [p04_all_nil [p :- (=> Nat Prop)]
     (All p (List.nil Nat))
     [(simp [All.nil])]]
    [p05_all_cons [p :- (=> Nat Prop), x :- Nat, xs :- (List Nat), hx :- (p x), ht :- (All p xs)]
     (All p (List.cons Nat x xs))
     [(constructor) (exact hx) (exact ht)]]
    [p06_all_head [p :- (=> Nat Prop), x :- Nat, xs :- (List Nat), h :- (All p (List.cons Nat x xs))]
     (p x)
     [(cases h) (exact hx)]]
    [p07_all_tail [p :- (=> Nat Prop), x :- Nat, xs :- (List Nat), h :- (All p (List.cons Nat x xs))]
     (All p xs)
     [(cases h) (exact ht)]]
    [p08_all_true [xs :- (List Nat)]
     (All (fn [x :- Nat] True) xs)
     [(induction xs) (constructor) (constructor) (trivial) (exact ih_tail)]]
    [p09_all_nonneg [xs :- (List Nat)]
     (All (fn [x :- Nat] (<= Nat 0 x)) xs)
     [(induction xs) (constructor) (constructor) (omega) (exact ih_tail)]]
    [p10_sorted_nil [n :- Nat]
     (Sorted n (List.nil Nat))
     [(constructor)]]
    [p11_sorted_single [n :- Nat, x :- Nat, h :- (<= n x)]
     (Sorted n (List.cons Nat x (List.nil Nat)))
     [(constructor) (exact h) (constructor)]]
    [p12_sorted_head [n :- Nat, x :- Nat, xs :- (List Nat), h :- (Sorted n (List.cons Nat x xs))]
     (<= n x)
     [(cases h) (exact hx)]]
    [p13_reach_refl [r :- (=> Nat Nat Prop), x :- Nat]
     (Reach r x x)
     [(constructor)]]
    [p14_reach_one [r :- (=> Nat Nat Prop), x :- Nat, y :- Nat, h :- (r x y)]
     (Reach r x y)
     [(exact (Reach.step r x y y h (Reach.refl r y)))]]
    [p15_reach_eq [x :- Nat, y :- Nat, h :- (Reach (fn [a :- Nat, b :- Nat] (= a b)) x y)]
     (= x y)
     [(induction h) (rfl) (simp_all)]]])

(def ^:private known-gaps
  {})

(deftest prop-inductive-conformance
  (cs/check-suite "prop/inductive"
                  (cs/run-suite 'ansatz.prop-inductive-conformance-test defs theorems)
                  known-gaps))
