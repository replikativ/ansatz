(ns ansatz.records-conformance-test
  "25 Lean scripts over an association-list model; reference: test/lean/records_conformance.lean.
  Translation follows list-conformance-test: constructor alternatives in order, list cons
  fields head/tail/ih_tail, <;> = and_then, record projections = keywords.
  rcases/obtain retain their Lean patterns to measure missing surface tactic support."
  (:refer-clojure :exclude [update remove distinct])
  (:require [clojure.test :refer [deftest]]
            [ansatz.conformance-support :as cs]))

(def ^:private defs
  '[(ansatz.core/structure Row [] (key Nat) (owner Nat) (active Bool) (value Nat))
    (ansatz.core/structure State [] (rows (List Row)) (owners (List Nat)))
    (ansatz.core/defn lookup [k :- Nat, xs :- (List Row)] Nat
      (match xs [nil 0] [(cons r t) (if (Nat.beq k (:key r)) (:value r) (lookup k t))]))
    (ansatz.core/defn update [k :- Nat, v :- Nat, xs :- (List Row)] (List Row)
      (match xs [nil (List.nil Row)]
             [(cons r t) (if (Nat.beq k (:key r))
                           (List.cons Row (Row.mk (:key r) (:owner r) (:active r) v) (update k v t))
                           (List.cons Row r (update k v t)))]))
    (ansatz.core/defn remove [k :- Nat, xs :- (List Row)] (List Row)
      (match xs [nil (List.nil Row)]
             [(cons r t) (if (Nat.beq k (:key r)) (remove k t) (List.cons Row r (remove k t)))]))
    (ansatz.core/defn pushRow [r :- Row, s :- State] State
      (State.mk (List.cons Row r (:rows s)) (:owners s)))
    (ansatz.core/defn enabled [xs :- (List Row)] (List Row)
      (match xs [nil (List.nil Row)]
             [(cons r t) (if (:active r) (List.cons Row r (enabled t)) (enabled t))]))
    (ansatz.core/defn values [xs :- (List Row)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons r t) (List.cons Nat (:value r) (values t))]))
    (ansatz.core/defn countRows [xs :- (List Row)] Nat
      (match xs [nil 0] [(cons r t) (+ (countRows t) 1)]))
    (ansatz.core/defn total [xs :- (List Row)] Nat
      (match xs [nil 0] [(cons r t) (+ (:value r) (total t))]))
    (ansatz.core/defn hasKey [k :- Nat, xs :- (List Row)] Bool
      (match xs [nil false] [(cons r t) (Bool.or (Nat.beq k (:key r)) (hasKey k t))]))
    (ansatz.core/defn distinct [xs :- (List Row)] Bool
      (match xs [nil true] [(cons r t) (Bool.and (Bool.not (hasKey (:key r) t)) (distinct t))]))
    (ansatz.core/defn memOwner [k :- Nat, xs :- (List Nat)] Bool
      (match xs [nil false] [(cons h t) (Bool.or (Nat.beq k h) (memOwner k t))]))
    (ansatz.core/defn ownersPresent [op :- (List Nat), xs :- (List Row)] Bool
      (match xs [nil true] [(cons r t) (Bool.and (memOwner (:owner r) op) (ownersPresent op t))]))
    ;; Function-valued recursion mirrors Lean exactly and keeps lo out of the fixed
    ;; recursion parameters (core/define-verified-impl requires those to stay unchanged).
    (ansatz.core/defn sortedFrom [xs :- (List Row)] (=> Nat Bool)
      (match xs [nil (fn [lo :- Nat] true)]
             [(cons r t) (fn [lo :- Nat] (Bool.and (Nat.ble lo (:key r)) (sortedFrom t (:key r))))]))])

(def ^:private theorems
  '[[r01_projection [k :- Nat, o :- Nat, v :- Nat, b :- Bool]
     (= (:owner (Row.mk k o b v)) o) [(rfl)]]
    [r02_eta [r :- Row] (= (Row.mk (:key r) (:owner r) (:active r) (:value r)) r)
     [(rcases r with [k o b v]) (rfl)]]
    [r03_obtain [r :- Row] (> (+ (:value r) 1) (:value r))
     [(obtain [k o b v] := r) (omega)]]
    [r04_match [r :- Row] (= (match r [(mk k o b v) v]) (:value r))
     [(cases r) (rfl)]]
    [r05_arithmetic [r :- Row, h :- (<= (:value r) (:key r))]
     (<= (+ (:value r) 2) (+ (:key r) 2)) [(omega)]]
    [r06_lookup_nil [k :- Nat] (= (lookup k (List.nil Row)) 0) [(simp [lookup])]]
    [r07_lookup_head [r :- Row, xs :- (List Row)]
     (= (lookup (:key r) (List.cons Row r xs)) (:value r)) [(simp [lookup])]]
    [r08_lookup_skip [k :- Nat, r :- Row, xs :- (List Row), h :- (= (Nat.beq k (:key r)) false)]
     (= (lookup k (List.cons Row r xs)) (lookup k xs)) [(simp [lookup h])]]
    [r09_update_nil [k :- Nat, v :- Nat] (= (update k v (List.nil Row)) (List.nil Row)) [(rfl)]]
    [r10_update_count [k :- Nat, v :- Nat, xs :- (List Row)]
     (= (countRows (update k v xs)) (countRows xs))
     [(induction xs) (simp [update countRows])
      (and_then (cases h (Nat.beq k (:key head))) (simp [update countRows h ih_tail]))]]
    [r11_remove_count [k :- Nat, xs :- (List Row)]
     (<= (countRows (remove k xs)) (countRows xs))
     [(induction xs) (simp [remove countRows])
      (and_then (and_then (cases h (Nat.beq k (:key head))) (simp [remove countRows h])) (omega))]]
    [r12_pushRow_count [r :- Row, s :- State]
     (= (countRows (:rows (pushRow r s))) (+ (countRows (:rows s)) 1)) [(rfl)]]
    [r13_values_head [r :- Row, xs :- (List Row)]
     (= (values (List.cons Row r xs)) (List.cons Nat (:value r) (values xs))) [(rfl)]]
    [r14_total_head [r :- Row, xs :- (List Row)]
     (= (total (List.cons Row r xs)) (+ (:value r) (total xs))) [(rfl)]]
    [r15_enabled_count [xs :- (List Row)] (<= (countRows (enabled xs)) (countRows xs))
     [(induction xs) (simp [enabled countRows])
      (and_then (and_then (cases h (:active head)) (simp [enabled countRows h])) (omega))]]
    [r16_enabled_idem [xs :- (List Row)] (= (enabled (enabled xs)) (enabled xs))
     [(induction xs) (simp [enabled])
      (and_then (cases h (:active head)) (simp [enabled h ih_tail]))]]
    [r17_hasKey_update [x :- Nat, k :- Nat, v :- Nat, xs :- (List Row)]
     (= (hasKey x (update k v xs)) (hasKey x xs))
     [(induction xs) (simp [update hasKey])
      (and_then (cases h (Nat.beq k (:key head))) (simp [update hasKey h ih_tail]))]]
    [r18_distinct_update [k :- Nat, v :- Nat, xs :- (List Row)]
     (= (distinct (update k v xs)) (distinct xs))
     [(induction xs) (simp [update distinct])
      (and_then (cases h (Nat.beq k (:key head))) (simp [update distinct h ih_tail r17_hasKey_update]))]]
    [r19_owners_update [op :- (List Nat), k :- Nat, v :- Nat, xs :- (List Row), h :- (= (ownersPresent op xs) true)]
     (= (ownersPresent op (update k v xs)) true)
     [(induction xs) (simp [update ownersPresent])
      (and_then (cases hk (Nat.beq k (:key head))) (simp_all [update ownersPresent]))]]
    [r20_sorted_update [lo :- Nat, k :- Nat, v :- Nat, xs :- (List Row)]
     (=> (= (sortedFrom xs lo) true) (= (sortedFrom (update k v xs) lo) true))
     [(induction xs generalizing lo) (simp [update sortedFrom]) (intro h)
      (and_then (cases hk (Nat.beq k (:key head))) (simp_all [update sortedFrom]))]]
    [r21_pushRow_distinct [r :- Row, s :- State, h :- (= (distinct (:rows s)) true), hk :- (= (hasKey (:key r) (:rows s)) false)]
     (= (distinct (:rows (pushRow r s))) true) [(simp [pushRow distinct h hk])]]
    [r22_pushRow_owners [r :- Row, s :- State, h :- (= (ownersPresent (:owners s) (:rows s)) true), ho :- (= (memOwner (:owner r) (:owners s)) true)]
     (= (ownersPresent (:owners (pushRow r s)) (:rows (pushRow r s))) true)
     [(simp [pushRow ownersPresent h ho])]]
    [r23_remove_owners [op :- (List Nat), k :- Nat, xs :- (List Row), h :- (= (ownersPresent op xs) true)]
     (= (ownersPresent op (remove k xs)) true)
     [(induction xs) (simp [ownersPresent] at h) (simp [remove ownersPresent])
      (and_then (cases hk (Nat.beq k (:key head))) (simp_all [remove ownersPresent]))]]
    [r24_closed []
     (= (lookup 2 (update 2 9 (List.cons Row (Row.mk 1 0 true 3) (List.cons Row (Row.mk 2 0 false 4) (List.nil Row))))) 9)
     [(decide)]]
    [r25_closed_invariants []
     (= (Bool.and
         (Bool.and (distinct (List.cons Row (Row.mk 1 0 true 3) (List.cons Row (Row.mk 2 0 false 4) (List.nil Row))))
                   (ownersPresent (List.cons Nat 0 (List.nil Nat)) (List.cons Row (Row.mk 1 0 true 3) (List.cons Row (Row.mk 2 0 false 4) (List.nil Row)))))
         (sortedFrom (List.cons Row (Row.mk 1 0 true 3) (List.cons Row (Row.mk 2 0 false 4) (List.nil Row))) 0)) true)
     [(decide)]]])

(def ^:private known-gaps {})

(deftest records-conformance
  (cs/check-suite "records" (cs/run-suite 'ansatz.records-conformance-test defs theorems) known-gaps))
