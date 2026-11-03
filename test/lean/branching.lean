import Init

example (n : Nat) (rule : ∀ x : Nat, True → x + 0 = x) : n + 0 = n := by
  rw [rule _ _]
  exact True.intro
example (n : Nat) (rule : ∀ x : Nat, True → x + 0 = x) : n + 0 = n := by
  rw [rule]
  exact True.intro
example (n : Nat) (p : Prop) (hp : p) (rule : ∀ x : Nat, True → x + 0 = x) :
    (n + 0 = n) ∧ p := by
  constructor
  · rewrite [rule _ _]
    · rfl
    · exact True.intro
  · exact hp
example (n : Nat) (rule : ∀ x : Nat, True → x + 0 = x) (hx : n = 1) : n + 0 = 1 := by
  rewrite [← rule n _] at hx
  · exact hx
  · exact True.intro
example (n : Nat) (rule : ∀ x y : Nat, y = 0 → x + 0 = x) : n + 0 = n := by
  rw [rule _ _ _]
  · exact 0
  · rfl
example (p : Prop) : p ∨ ¬p := by
  by_cases hp : p
  case pos => exact Or.inl hp
  case neg => exact Or.inr hp
example (p q : Prop) (hq : q) : (p ∨ ¬p) ∧ q := by
  constructor
  · by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr hp
  · exact hq
example (p : Prop) (d : Decidable p) : p ∨ ¬p := by
  by_cases hp : p
  · exact Or.inl hp
  · exact Or.inr hp
example (p : Prop) : p ∨ ¬p := by
  by_cases p
  · rename_i h
    exact Or.inl h
  · rename_i h
    exact Or.inr h
-- Ansatz's Bool path retains false-first constructor order.
example (b : Bool) : b = false ∨ b = true := by
  cases hb : b
  · exact Or.inl rfl
  · exact Or.inr rfl
example (b : Bool) (h : (if b then 0 else 1) = (0 : Nat)) : b = true := by
  split at h
  · assumption
  · cases h
example (b : Bool) (_unused : True) (h : (if b then 0 else 1) = (0 : Nat)) : b = true := by
  split at *
  · assumption
  · cases h
example (b : Bool) (h : (match b with | true => 0 | false => 1) = (0 : Nat)) : b = true := by
  split at h
  · rfl
  · cases h

example (p : Prop) (d : Decidable p) (hh : @ite Nat p d 0 1 = 0) : p := by
  split at hh
  · assumption
  · cases hh
example (b : Bool) (h : (if b then 0 else 1) = (0 : Nat)) (hh : h = h) :
    b = true ∧ h = h := by
  split at h
  · exact ⟨by assumption, hh⟩
  · cases h
example (n : Nat) (rule : ∀ x y : Nat, y = 0 → x + 0 = x) : n + 0 = n := by
  rw [rule _ _ _]
  all_goals try rfl

example (b : Bool) (n : Nat) (_unused : True) : (if b then n else n) = n := by
  split at ⊢ <;> rfl
example (b : Bool) (n : Nat) (_unused : True) : (if b then n else n) = n := by
  split at * <;> rfl

example (b : Bool) (h : (match b with | true => 0 | false => 1) = (0 : Nat))
    (hh : h = h) : b = true ∧ h = h := by
  split at h
  · exact ⟨rfl, hh⟩
  · cases h
