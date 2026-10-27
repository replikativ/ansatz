set_option linter.unusedVariables false
-- Lean 4.33.1, Init only. split_ifs is paired with repeated core split.
example (x y : Nat) (h : x = y) (hx : x = 1) : y = 1 := by
  rw [h] at hx
  exact hx
example (x y : Nat) (h : x = y) (hx : x = 1) (hx2 : x = 2) : x = 1 ∧ x = 2 := by
  rw [h] at hx hx2 ⊢
  exact ⟨hx, hx2⟩
example (x y : Nat) (h : x = y) (hx : x = 1) : y = 1 := by
  rw [h] at *
  exact hx
example (x y z : Nat) (hx : x + (y + z) = 1) : (x + y) + z = 1 := by
  rw [← Nat.add_assoc] at hx
  exact hx
example (x y : Nat) (h : x = y) (hx : x = 1) (hh : hx = hx) : y = 1 := by
  rw [h] at hx
  exact hx
example (b x y : Bool) (ht : b = true → x = true) (hf : b = false → y = true) :
    (if b then x else y) = true := by
  cases b <;> simp_all
example (b : Bool) (p : Bool → Prop) (h1 : p b)
    (q : p b → Prop) (h2 : q h1) : q h1 := by
  fail_if_success have h1_special : p false := h1
  cases b
  case false =>
    have h1_special : p false := h1
    have h2_special : q h1_special := h2
    exact h2_special
  case true =>
    have h1_special : p true := h1
    have h2_special : q h1_special := h2
    exact h2_special
example (b : Bool) (p : Nat → Bool) (n : Nat) : p (if b then n else n) = p n := by
  repeat' split
  all_goals rfl
example (b c : Bool) (p : Nat → Bool) (n : Nat) : p (if b then (if c then n else n) else n) = p n := by
  repeat' split
  all_goals rfl
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (0 + k) = Nat.succ k
    exact congrArg Nat.succ ih
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h
  case inr hq => exact Or.inl hq
  case inl hp => exact Or.inr hp
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h
  next hp => exact Or.inr hp
  next hq => exact Or.inl hq
example (p : Prop) (hp : p) : True ∧ p := by
  constructor
  any_goals exact hp
  constructor
example (p : Prop) : p → p := by
  intro
  assumption
example : True := by
  -- `simp_all at *` is rejected by the parser: simp_all has no location syntax.
  constructor
example (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
  constructor
  all_goals constructor
  exact hp
  exact hq
  exact hq
  exact hp
example (p q : Prop) (hp : p) (hq : q) : (p ∧ p) ∧ q := by
  constructor
  constructor <;> exact hp
  exact hq
example (xs : List Nat) : xs = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
    change h :: t = h :: t
    exact congrArg (fun ys => h :: ys) ih
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  fail_if_success all_goals exact hp
  exact hp
  exact hq
example (xs : List Nat) : xs = xs := by
  cases xs with
  | nil => rfl
  | cons h t =>
    change h :: t = h :: t
    rfl
example (b c : Bool) : b = b := by
  cases b
  cases c
  case false.true => rfl
  case false.false => rfl
  case true => rfl
example (p : Prop) : p → p := by
  intro _
  assumption
inductive CaseShape where
  | base
  | node (prev : CaseShape)
inductive LocalEvidence : CaseShape → Prop where
  | zero : LocalEvidence CaseShape.base
  | step (n : CaseShape) : LocalEvidence (CaseShape.node n)
example (n : CaseShape) (h : LocalEvidence (CaseShape.node n)) (hh : h = h) : n = n := by
  cases h
  rfl
example (b : Bool) (hb : b = true) : (if b then (0 : Nat) else 1) = 0 := by
  repeat' split
  all_goals simp_all

example (b : Bool) : ((if b then (0 : Nat) else 1) = (if b then 0 else 1)) ∧ True := by
  constructor
  (split <;> rfl)
  constructor
example (n : Nat) : n = n := by
  induction n with
  | zero => rfl
  | succ k =>
    change Nat.succ k = Nat.succ k
    rfl
example (p : Prop) (hp : p) (n : Nat) : p → n = n := by
  intro
  induction n with
  | zero => rfl
  | succ k =>
    change Nat.succ k = Nat.succ k
    rfl

inductive BranchOrder where
  | leaf
  | node (prev : BranchOrder) (value : Nat)
example (x : BranchOrder) : x = x := by
  induction x with
  | leaf => rfl
  | node child value =>
    change BranchOrder.node child value = BranchOrder.node child value
    rfl

example (i j : Nat) (p : Nat → Prop) (ht : p 10) (hf : p 20) :
    p (if i = j then 10 else 20) := by
  split <;> assumption
example (c : Prop) [Decidable c] (p : Nat → Prop) (t : c → Nat) (f : ¬c → Nat)
    (ht : ∀ h, p (t h)) (hf : ∀ h, p (f h)) : p (dite c t f) := by
  split <;> first | apply ht | apply hf
example (i j : Nat) (h : i = j) (p : Nat → Prop) (hp : p i) :
    p (if i = j then i else j) := by
  rw [if_pos h]
  exact hp
example (c : Prop) [Decidable c] (h : ¬c) (x y : Nat) (p : Nat → Prop) (hp : p y) :
    p (ite c x y) := by
  rw [if_neg h]
  exact hp
example (i j n : Nat) (p : Nat → Nat → Nat → Prop) (lemma : ∀ x y z, p x y z) :
    p i j n := by
  apply (lemma _ j n)
example (p q : Nat → Prop) (n : Nat) (hp : p n) (hq : q n) (irrelevant : True)
    (lemma : ∀ x, p x → q x → True) : True := by
  apply (lemma _)
  assumption
  assumption
inductive RenameShape where
  | base
  | node (prev : RenameShape)
inductive ScopedEvidence : RenameShape → Prop where
  | base : ScopedEvidence RenameShape.base
  | mk (n : RenameShape) (hi : n = n) : ScopedEvidence (RenameShape.node n)
example (n : RenameShape) (h : ScopedEvidence (RenameShape.node n)) : n = n := by
  cases h
  rename_i hi
  exact hi
example (n m : Nat) (h : m = n) (hh : h = h) : 0 + m = n := by
  induction n generalizing m <;> rw [h] <;> simp
example (i j x y : Nat) : (if i = j then x else y) = (if i = j then x else y) ∧ True := by
  constructor
  split
  · rfl
  · rfl
  · constructor
example (p q : Prop) (h : p ∧ q) : q := by
  cases h
  rename_i hq
  exact hq
example (p : Prop) : p → p := by
  intro
  rename_i h
  exact h
inductive CountEvidence : Nat → Prop where
  | zero : CountEvidence 0
  | step (n : Nat) (h : CountEvidence n) : CountEvidence (Nat.succ n)
example (n : Nat) (h : CountEvidence n) (m : Nat) (hm : m = n) (hh : hm = hm) :
    0 + m = n := by
  induction h generalizing m <;> rw [hm] <;> simp
example (c : Prop) [Decidable c] (p : Nat → Nat → Prop)
    (ht : ∀ n, p n n) (hf : ∀ n, p n 0) : ∀ n, p n (ite c n 0) := by
  split <;> intro n <;> first | apply ht | apply hf
example (f g k h : Nat → Nat) (p : Nat → Prop) (n : Nat)
    (first_rule : ∀ x, f x = g (k x)) (second_rule : ∀ y, g y = h y)
    (third_rule : ∀ z, h z = z) (hp : p (k n)) : p (f n) := by
  rw [first_rule, second_rule, third_rule]
  exact hp
