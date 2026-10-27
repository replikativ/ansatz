(ns ansatz.option-prod-conformance-test
  "Direct translations of test/lean/option_prod_conformance.lean.
  Uses list-conformance-test translation rules; explicit type arguments spell Lean @ applications.
  Constructor branches use ansatz field names. No alternative proof scripts for gaps."
  (:refer-clojure :exclude [first find partition])
  (:require [clojure.test :refer [deftest]]
            [ansatz.conformance-support :as cs]))

;; Lean reference: src/Lean/Elab/Tactic/{Induction,Simp,Decide}.lean,
;; evalInductionCore/evalCasesCore, evalSimp, evalDecideCore.
(def ^:private defs
  '[(ansatz.core/defn first [xs :- (List Nat)] (Option Nat) (match xs [nil (Option.none Nat)] [(cons h t) (Option.some Nat h)]))
    (ansatz.core/defn find [p :- (=> Nat Bool), xs :- (List Nat)] (Option Nat) (match xs [nil (Option.none Nat)] [(cons h t) (if (p h) (Option.some Nat h) (find p t))]))
    (ansatz.core/defn lookup [k :- Nat, xs :- (List (Prod Nat Nat))] (Option Nat) (match xs [nil (Option.none Nat)] [(cons h t) (if (Nat.beq k (Prod.fst Nat Nat h)) (Option.some Nat (Prod.snd Nat Nat h)) (lookup k t))]))
    (ansatz.core/defn unpack [o :- (Option Nat)] Nat (match o [none 0] [(some x) x]))
    (ansatz.core/defn swap [p :- (Prod Nat Nat)] (Prod Nat Nat) (Prod.mk Nat Nat (Prod.snd Nat Nat p) (Prod.fst Nat Nat p)))
    (ansatz.core/defn unzip [xs :- (List (Prod Nat Nat))] (Prod (List Nat) (List Nat)) (match xs [nil (Prod.mk (List Nat) (List Nat) (List.nil Nat) (List.nil Nat))] [(cons h t) (Prod.mk (List Nat) (List Nat) (List.cons Nat (Prod.fst Nat Nat h) (Prod.fst (List Nat) (List Nat) (unzip t))) (List.cons Nat (Prod.snd Nat Nat h) (Prod.snd (List Nat) (List Nat) (unzip t))))]))
    (ansatz.core/defn partition [p :- (=> Nat Bool), xs :- (List Nat)] (Prod (List Nat) (List Nat)) (match xs [nil (Prod.mk (List Nat) (List Nat) (List.nil Nat) (List.nil Nat))] [(cons h t) (if (p h) (Prod.mk (List Nat) (List Nat) (List.cons Nat h (Prod.fst (List Nat) (List Nat) (partition p t))) (Prod.snd (List Nat) (List Nat) (partition p t))) (Prod.mk (List Nat) (List Nat) (Prod.fst (List Nat) (List Nat) (partition p t)) (List.cons Nat h (Prod.snd (List Nat) (List Nat) (partition p t)))))]))])

(def ^:private theorems
  '[[o01_first_nil []
     (= (first (List.nil Nat)) (Option.none Nat))
     [(rfl)]]
    [o02_first_cons [x :- Nat, xs :- (List Nat)]
     (= (first (List.cons Nat x xs)) (Option.some Nat x))
     [(simp [first])]]
    [o03_find_false [xs :- (List Nat)]
     (= (find (fn [x :- Nat] false) xs) (Option.none Nat))
     [(and_then (induction xs) (simp [find *]))]]
    [o04_find_true [xs :- (List Nat)]
     (= (find (fn [x :- Nat] true) xs) (first xs))
     [(and_then (cases xs) (simp [find first]))]]
    [o05_find_hit [p :- (=> Nat Bool), x :- Nat, xs :- (List Nat), h :- (= (p x) true)]
     (= (find p (List.cons Nat x xs)) (Option.some Nat x))
     [(simp [find h])]]
    [o06_find_match [p :- (=> Nat Bool), xs :- (List Nat)]
     (= (unpack (find p xs)) (match (find p xs) [none 0] [(some x) x]))
     [(and_then (cases h (find p xs)) (simp [unpack]))]]
    [o07_map_id [xs :- (List Nat)]
     (= (Option.map Nat Nat (fn [x :- Nat] x) (first xs)) (first xs))
     [(and_then (cases h (first xs)) (simp [Option.map]))]]
    [o08_lookup_nil [k :- Nat]
     (= (lookup k (List.nil (Prod Nat Nat))) (Option.none Nat))
     [(rfl)]]
    [o09_lookup_hit [k :- Nat, v :- Nat, xs :- (List (Prod Nat Nat))]
     (= (lookup k (List.cons (Prod Nat Nat) (Prod.mk Nat Nat k v) xs)) (Option.some Nat v))
     [(simp [lookup])]]
    [o10_swap_twice [p :- (Prod Nat Nat)]
     (= (swap (swap p)) p)
     [(obtain [a b] := p) (rfl)]]
    [o11_swap_fields [p :- (Prod Nat Nat)]
     (= (+ (Prod.fst Nat Nat (swap p)) (Prod.snd Nat Nat (swap p))) (+ (Prod.fst Nat Nat p) (Prod.snd Nat Nat p)))
     [(rcases p [a b]) (simp [swap Nat.add_comm])]]
    [o12_unzip_nil []
     (= (unzip (List.nil (Prod Nat Nat))) (Prod.mk (List Nat) (List Nat) (List.nil Nat) (List.nil Nat)))
     [(rfl)]]
    [o13_unzip_cons [a :- Nat, b :- Nat, xs :- (List (Prod Nat Nat))]
     (= (Prod.fst (List Nat) (List Nat) (unzip (List.cons (Prod Nat Nat) (Prod.mk Nat Nat a b) xs))) (List.cons Nat a (Prod.fst (List Nat) (List Nat) (unzip xs))))
     [(simp [unzip])]]
    [o14_partition_false [xs :- (List Nat)]
     (= (Prod.fst (List Nat) (List Nat) (partition (fn [x :- Nat] false) xs)) (List.nil Nat))
     [(and_then (induction xs) (simp [partition *]))]]
    [o15_partition_true [xs :- (List Nat)]
     (= (Prod.fst (List Nat) (List Nat) (partition (fn [x :- Nat] true) xs)) xs)
     [(and_then (induction xs) (simp [partition *]))]]])

(def ^:private known-gaps
  {})

(deftest option-prod-conformance
  (cs/check-suite "option/prod"
                  (cs/run-suite 'ansatz.option-prod-conformance-test defs theorems)
                  known-gaps))
