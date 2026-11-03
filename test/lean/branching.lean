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

example (p : Prop) (d : Decidable p) (hh : @ite Nat p d 0 1 = 0)
    (_dep : hh = hh) : hh = hh := by
  split at hh <;> rfl
example (p : Prop) (d : Decidable p) (hh : @ite Prop p d True True) : True := by
  split at hh <;> exact hh
example (rule : [Inhabited Nat] → 1 + 0 = 1) : 1 + 0 = 1 := by
  rw [rule]
example (_rule : [Inhabited False] → 1 + 0 = 1) : 1 + 0 = 1 := by
  fail_if_success rw [_rule]
  rfl
example (n : Nat) (_dep : n = n) (_unused : True) : n = n := by
  fail_if_success clear n
  clear _unused
  rfl

example (hh : True ∧ False) : False := by simp at hh

example (rule : ∀ {α : Type}, [HAdd Nat Nat α] → 1 + 0 = (1 : Nat)) : 1 + 0 = (1 : Nat) := by
  rw [rule]
example (rule : ∀ {α : Type}, [HAdd Nat Nat α] → 1 + 0 = (1 : Nat)) : 1 + 0 = (1 : Nat) := by
  apply rule
example (_bad : [Inhabited False] → True) (good : [Inhabited Nat] → True) : True := by
  first | apply _bad | apply good
example (_bad : [Inhabited False] → 1 + 0 = (1 : Nat))
    (good : [Inhabited Nat] → 1 + 0 = (1 : Nat)) : 1 + 0 = (1 : Nat) := by
  first | rw [_bad] | rw [good]
example (p : Prop) (d : Decidable p) (hh : @ite Nat p d 0 1 = 0) : p := by
  split at hh
  · assumption
  · cases hh
example (p q : Prop) (dp : Decidable p) (dq : Decidable q)
    (hh : @ite Prop p dp True True) (_other : @ite Prop q dq True True) : hh = hh := by
  split at *
  all_goals
    guard_hyp hh : @ite Prop p dp True True
    guard_hyp _other : True
    rfl

example (i j x y : Nat) : ((if i = j then x else y) = (if i = j then x else y)) ∧ True := by
  constructor
  · split
    · guard_target = x = x
      rfl
    · guard_target = y = y
      rfl
  · exact True.intro

example [_boolAdd : HAdd Nat Nat Bool]
    (_rule : ∀ {α : Type}, [HAdd Nat Nat α] → α → α) : Nat := by
  fail_if_success apply _rule
  exact 0
