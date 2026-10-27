(ns ansatz.bool-decide-conformance-test
  "25 Lean Bool/decide scripts; reference: test/lean/bool_decide_conformance.lean.
  Translation follows list-conformance-test. Bool operators are Bool.and/or/not;
  Prop comparisons in statements stay <=/<, while if's comparison compiles to Nat.ble
  and Bool.rec (Lean uses a decidable Prop ite). bleLow explicitly tests Bool code.
  h.1 translates to And.left with its implicit propositions."
  (:require [clojure.test :refer [deftest]]
            [ansatz.conformance-support :as cs]))

(def ^:private defs
  '[(ansatz.core/defn ready [a :- Bool, b :- Bool] Bool (Bool.and a (Bool.not b)))
    (ansatz.core/defn allowed [a :- Bool, b :- Bool] Bool (Bool.or a b))
    (ansatz.core/defn low [x :- Nat, y :- Nat] Nat (if (<= x y) x y))
    (ansatz.core/defn same [x :- Nat, y :- Nat] Bool (if (Nat.beq x y) true false))
    (ansatz.core/defn bleLow [x :- Nat, y :- Nat] Nat (if (Nat.ble x y) x y))])

(def ^:private theorems
  '[[b01_ready_false [a :- Bool] (= (ready a false) a) [(simp [ready])]]
    [b02_ready_true [a :- Bool] (= (ready a true) false) [(simp [ready])]]
    [b03_allowed_false [a :- Bool] (= (allowed a false) a) [(simp [allowed])]]
    [b04_allowed_true [a :- Bool] (= (allowed a true) true) [(simp [allowed])]]
    [b05_ready_idem [a :- Bool, b :- Bool] (= (ready (ready a b) b) (ready a b))
     [(and_then (and_then (cases a) (cases b)) (simp [ready]))]]
    [b06_allowed_comm [a :- Bool, b :- Bool] (= (allowed a b) (allowed b a))
     [(and_then (and_then (cases a) (cases b)) (simp [allowed]))]]
    [b07_demorgan [a :- Bool, b :- Bool]
     (= (Bool.not (allowed a b)) (Bool.and (Bool.not a) (Bool.not b)))
     [(and_then (and_then (cases a) (cases b)) (simp [allowed]))]]
    [b08_double_not [a :- Bool, b :- Bool] (= (Bool.not (Bool.not (ready a b))) (ready a b)) [(simp)]]
    [b09_and_true [a :- Bool, b :- Bool, h :- (= (Bool.and a b) true)] (= a true)
     [(simp [Bool.and_eq_true] at h) (exact (And.left (= a true) (= b true) h))]]
    [b10_ready_hyp [a :- Bool, b :- Bool, h :- (= (ready a b) true)] (= a true)
     [(and_then (and_then (cases a) (cases b)) (simp_all [ready]))]]
    [b11_or_false [a :- Bool, b :- Bool] (=> (= (allowed a b) false) (= a false))
     [(and_then (and_then (cases a) (cases b)) (simp [allowed]))]]
    [b12_low_refl [x :- Nat] (= (low x x) x) [(simp [low])]]
    [b13_low_of_le [x :- Nat, y :- Nat, h :- (<= x y)] (= (low x y) x) [(simp [low h])]]
    [b14_low_of_gt [x :- Nat, y :- Nat, h :- (< y x)] (= (low x y) y)
     [(have hnot (Not (<= x y))) (omega) (simp [low hnot])]]
    [b15_bleLow_refl [x :- Nat] (= (bleLow x x) x) [(simp [bleLow])]]
    [b16_ble_bridge [x :- Nat, y :- Nat, h :- (<= x y)] (= (Nat.ble x y) true) [(simp [Nat.ble_eq h])]]
    [b17_beq_bridge [x :- Nat, y :- Nat, h :- (= x y)] (= (same x y) true) [(simp [same h])]]
    [b18_beq_refl [x :- Nat] (= (same x x) true) [(simp [same])]]
    [b19_closed_le [] (<= Nat 3 7) [(decide)]]
    [b20_closed_not_le [] (Not (<= Nat 7 3)) [(decide)]]
    [b21_closed_code [] (And (= (low 9 4) 4) (= (same 3 3) true)) [(decide)]]
    [b22_decide_subst [x :- Nat, y :- Nat, hx :- (= x 3), hy :- (= y 7)] (<= x y)
     [(subst hx) (subst hy) (decide)]]
    [b23_decide_subst_zero [x :- Nat, hx :- (= x 0)] (<= x 5) [(subst hx) (decide)]]
    [b24_cases_comparison [x :- Nat, y :- Nat] (Or (= (bleLow x y) x) (= (bleLow x y) y))
     [(and_then (cases h (Nat.ble x y)) (simp [bleLow h]))]]
    [b25_prop_bool [x :- Nat, y :- Nat, h :- (= (Nat.ble x y) true)] (<= x y)
     [(simp [Nat.ble_eq] at h) (exact h)]]])

(def ^:private known-gaps
  '{b14_low_of_gt "Phase-2D encoding: low uses Nat.ble/Bool.rec, but hnot negates Prop LE.le. Lean uses Prop ite; no generic negated-Prop-to-Bool bridge is present."})

(deftest bool-decide-conformance
  (cs/check-suite "bool/decide" (cs/run-suite 'ansatz.bool-decide-conformance-test defs theorems) known-gaps))
