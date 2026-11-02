import Lean

example (b : Bool) : b = b ∧ b = b := by
  constructor
  · cases b <;> rfl
  · exact Eq.refl b

example (b : Bool) : b = b ∧ b = b := by
  constructor
  all_goals cases b
  all_goals rfl

example (n : Nat) : n = n := by
  cases n with
  | zero => rfl
  | succ k => exact Eq.refl (Nat.succ k)

inductive CasesChain : Prop where
  | base
  | step (hx : CasesChain)

example (h : CasesChain) : CasesChain := by
  cases h with
  | base => exact CasesChain.base
  | step hx => exact hx

inductive CasesIndexed : Nat → Prop where
  | mk (x : Nat) : CasesIndexed (Nat.succ x)

example (f : Nat) (h : CasesIndexed (Nat.succ f)) : f = f := by
  cases h
  exact Eq.refl f

example (n : Nat) (P : Nat → Prop) (h : P n) : P n := by
  cases n with
  | zero => exact h
  | succ k => exact h

example (n : Nat) (P : Nat → Prop) (h : ∀ k, n = k → P k) : P n := by
  cases eqn : n with
  | zero => exact h 0 eqn
  | succ k => exact h (Nat.succ k) eqn

inductive CasesVec (A : Type) : Nat → Type where
  | nil : CasesVec A Nat.zero
  | cons (x : A) (n : Nat) (xs : CasesVec A n) : CasesVec A (Nat.succ n)

example (n : Nat) (v : CasesVec Nat (Nat.succ n)) : n = n := by
  cases v
  exact Eq.refl n

example (x y : Nat) (h : x = y) : x = y := by
  cases h
  exact Eq.refl x

inductive CaseShape where
  | base
  | node (prev : CaseShape)
inductive LocalEvidence : CaseShape → Prop where
  | zero : LocalEvidence CaseShape.base
  | step (k : CaseShape) : LocalEvidence (CaseShape.node k)
example (n : CaseShape) (h : LocalEvidence (CaseShape.node n)) (hh : h = h) : n = n := by
  cases h
  exact Eq.refl n

example (f : Nat) (h : CasesIndexed (Nat.succ f)) : f = f := by
  cases h with
  | mk x => exact Eq.refl f

example (f : Nat) (h : CasesIndexed (Nat.succ f)) : f = f := by
  rcases h with ⟨x⟩
  exact Eq.refl f

example (v : CasesVec Nat (Nat.succ Nat.zero)) : ∃ x : Nat, x = x := by
  cases v with
  | cons x k xs =>
    have tail : CasesVec Nat Nat.zero := xs
    exact ⟨x, Eq.refl x⟩

example (x : Nat) (h : HEq x x) : x = x := by
  cases h
  exact Eq.refl x

example (v : CasesVec Nat (Nat.succ Nat.zero)) : ∃ x : Nat, x = x := by
  rcases v with ⟨⟩ | ⟨x, k, xs⟩
  have tail : CasesVec Nat Nat.zero := xs
  exact ⟨x, Eq.refl x⟩

example (n m : Nat) (h : Nat.le n m) : Nat.le n m := by
  cases h with
  | refl => exact Nat.le_refl n
  | step hp => exact Nat.le.step hp

example (n m : Nat) (h : Nat.le n m) : Nat.le n m := by
  cases h with
  | refl => exact Nat.le_refl n
  | @step k hp =>
    have bound : Nat.le n k := hp
    exact Nat.le.step bound

example (x : Nat) (h : x = x) : x = x := by
  cases h
  exact Eq.refl x

example (x : Nat) (h : x = x) : True := by
  cases h
  exact True.intro

example (x : Nat) (h : x = x) : h = h := by
  cases h
  exact Eq.refl (Eq.refl x)

example (x : Nat) (h : Nat.add x Nat.zero = x) : x = x := by
  cases h
  exact Eq.refl x

example (x y : Nat) (h : HEq x y) : x = y := by
  cases h
  exact Eq.refl x

inductive CasesFixed (n : Nat) : Nat → Prop where
  | refl : CasesFixed n n

example (n : Nat) (h : CasesFixed n n) : n = n := by
  cases h
  exact Eq.refl n

example (x : Nat) (h : x = x) (hh : h = h) : h = h := by
  cases h
  exact hh
