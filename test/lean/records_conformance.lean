-- Reference for ansatz.records-conformance-test; Lean 4.33.1, Init only.
-- Scripts exercise Lean.Elab.Tactic.Induction.evalInduction/evalCases,
-- RCases.evalRCases/evalObtain, and Decide.evalDecideCore.
structure Row where
  key : Nat
  owner : Nat
  active : Bool
  value : Nat
structure State where
  rows : List Row
  owners : List Nat

def lookup (k : Nat) : List Row → Nat
  | [] => 0
  | r :: t => if Nat.beq k r.key then r.value else lookup k t
def update (k v : Nat) : List Row → List Row
  | [] => []
  | r :: t => if Nat.beq k r.key then Row.mk r.key r.owner r.active v :: update k v t else r :: update k v t
def remove (k : Nat) : List Row → List Row
  | [] => []
  | r :: t => if Nat.beq k r.key then remove k t else r :: remove k t
def pushRow (r : Row) (s : State) : State := ⟨r :: s.rows, s.owners⟩
def enabled : List Row → List Row
  | [] => []
  | r :: t => if r.active then r :: enabled t else enabled t
def values : List Row → List Nat
  | [] => []
  | r :: t => r.value :: values t
def countRows : List Row → Nat
  | [] => 0
  | _ :: t => countRows t + 1
def total : List Row → Nat
  | [] => 0
  | r :: t => r.value + total t
def hasKey (k : Nat) : List Row → Bool
  | [] => false
  | r :: t => Nat.beq k r.key || hasKey k t
def distinct : List Row → Bool
  | [] => true
  | r :: t => !hasKey r.key t && distinct t
def memOwner (k : Nat) : List Nat → Bool
  | [] => false
  | h :: t => Nat.beq k h || memOwner k t
def ownersPresent (op : List Nat) : List Row → Bool
  | [] => true
  | r :: t => memOwner r.owner op && ownersPresent op t
-- Adjacent ordering via a lower bound, avoiding partial List.head.
def sortedFrom (xs : List Row) : Nat → Bool :=
  match xs with
  | [] => fun _ => true
  | r :: t => fun lo => Nat.ble lo r.key && sortedFrom t r.key

theorem r01_projection (k o v : Nat) (b : Bool) : (Row.mk k o b v).owner = o := by rfl
theorem r02_eta (r : Row) : Row.mk r.key r.owner r.active r.value = r := by
  rcases r with ⟨k, o, b, v⟩
  rfl
theorem r03_obtain (r : Row) : r.value + 1 > r.value := by
  obtain ⟨k, o, b, v⟩ := r
  omega
theorem r04_match (r : Row) : (match r with | ⟨_, _, _, v⟩ => v) = r.value := by
  cases r
  rfl
theorem r05_arithmetic (r : Row) (h : r.value ≤ r.key) : r.value + 2 ≤ r.key + 2 := by omega
theorem r06_lookup_nil (k : Nat) : lookup k [] = 0 := by simp [lookup]
theorem r07_lookup_head (r : Row) (xs : List Row) : lookup r.key (r :: xs) = r.value := by simp [lookup]
theorem r08_lookup_skip (k : Nat) (r : Row) (xs : List Row) (h : Nat.beq k r.key = false) : lookup k (r :: xs) = lookup k xs := by simp [lookup, h]
theorem r09_update_nil (k v : Nat) : update k v [] = [] := by rfl
theorem r10_update_count (k v : Nat) (xs : List Row) : countRows (update k v xs) = countRows xs := by
  induction xs with
  | nil => simp [update, countRows]
  | cons r t ih => cases h : Nat.beq k r.key <;> simp [update, countRows, h, ih]
theorem r11_remove_count (k : Nat) (xs : List Row) : countRows (remove k xs) ≤ countRows xs := by
  induction xs with
  | nil => simp [remove, countRows]
  | cons r t ih => cases h : Nat.beq k r.key <;> simp [remove, countRows, h] <;> omega
theorem r12_pushRow_count (r : Row) (s : State) : countRows (pushRow r s).rows = countRows s.rows + 1 := by rfl
theorem r13_values_head (r : Row) (xs : List Row) : values (r :: xs) = r.value :: values xs := by rfl
theorem r14_total_head (r : Row) (xs : List Row) : total (r :: xs) = r.value + total xs := by rfl
theorem r15_enabled_count (xs : List Row) : countRows (enabled xs) ≤ countRows xs := by
  induction xs with
  | nil => simp [enabled, countRows]
  | cons r t ih => cases h : r.active <;> simp [enabled, countRows, h] <;> omega
theorem r16_enabled_idem (xs : List Row) : enabled (enabled xs) = enabled xs := by
  induction xs with
  | nil => simp [enabled]
  | cons r t ih => cases h : r.active <;> simp [enabled, h, ih]
theorem r17_hasKey_update (x k v : Nat) (xs : List Row) : hasKey x (update k v xs) = hasKey x xs := by
  induction xs with
  | nil => simp [update, hasKey]
  | cons r t ih => cases h : Nat.beq k r.key <;> simp [update, hasKey, h, ih]
theorem r18_distinct_update (k v : Nat) (xs : List Row) : distinct (update k v xs) = distinct xs := by
  induction xs with
  | nil => simp [update, distinct]
  | cons r t ih => cases h : Nat.beq k r.key <;> simp [update, distinct, h, ih, r17_hasKey_update]
theorem r19_owners_update (op : List Nat) (k v : Nat) (xs : List Row) (h : ownersPresent op xs = true) : ownersPresent op (update k v xs) = true := by
  induction xs with
  | nil => simp [update, ownersPresent]
  | cons r t ih => cases hk : Nat.beq k r.key <;> simp_all [update, ownersPresent]
theorem r20_sorted_update (lo k v : Nat) (xs : List Row) : sortedFrom xs lo = true → sortedFrom (update k v xs) lo = true := by
  induction xs generalizing lo with
  | nil => simp [update, sortedFrom]
  | cons r t ih =>
    intro h
    cases hk : Nat.beq k r.key <;> simp_all [update, sortedFrom]
theorem r21_pushRow_distinct (r : Row) (s : State) (h : distinct s.rows = true) (hk : hasKey r.key s.rows = false) : distinct (pushRow r s).rows = true := by simp [pushRow, distinct, h, hk]
theorem r22_pushRow_owners (r : Row) (s : State) (h : ownersPresent s.owners s.rows = true) (ho : memOwner r.owner s.owners = true) : ownersPresent (pushRow r s).owners (pushRow r s).rows = true := by simp [pushRow, ownersPresent, h, ho]
theorem r23_remove_owners (op : List Nat) (k : Nat) (xs : List Row) (h : ownersPresent op xs = true) : ownersPresent op (remove k xs) = true := by
  induction xs with
  | nil => simp [ownersPresent] at h; simp [remove, ownersPresent]
  | cons r t ih => cases hk : Nat.beq k r.key <;> simp_all [remove, ownersPresent]
theorem r24_closed : lookup 2 (update 2 9 [⟨1, 0, true, 3⟩, ⟨2, 0, false, 4⟩]) = 9 := by decide
theorem r25_closed_invariants : distinct [⟨1, 0, true, 3⟩, ⟨2, 0, false, 4⟩] && ownersPresent [0] [⟨1, 0, true, 3⟩, ⟨2, 0, false, 4⟩] && sortedFrom [⟨1, 0, true, 3⟩, ⟨2, 0, false, 4⟩] 0 = true := by decide
