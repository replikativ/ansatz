-- Lean counterpart of test/ansatz/tactic/unfold_test.clj (Lean 4.33.1, Init only).
-- `unfold f` delta-expands a non-recursive `f` and leaves other definitions folded.

structure UnfoldSt where
  hs : List Nat
  es : List Nat

def unfoldHcov : List Nat → List Nat → Bool
  | [], _ => true
  | h :: t, es => (h == 0) && unfoldHcov t es

def unfoldWrap (s : UnfoldSt) : Bool := unfoldHcov s.hs s.es

theorem unfoldWrap_of_hcov (f : UnfoldSt → UnfoldSt) (s : UnfoldSt)
    (h : unfoldHcov (f s).hs (f s).es = true) : unfoldWrap (f s) = true := by
  unfold unfoldWrap
  rw [h]

theorem unfoldWrap_exact (xs ys : List Nat) (h : unfoldHcov xs ys = true) :
    unfoldWrap ⟨xs, ys⟩ = true := by
  unfold unfoldWrap
  exact h

def unfoldTwice (n : Nat) : Nat := n + n

theorem unfoldTwice_forall : ∀ n : Nat, unfoldTwice n = n + n := by
  unfold unfoldTwice
  intro n
  rfl

-- unfolding a constant that does not occur fails
example (n : Nat) : n = n := by
  fail_if_success unfold unfoldTwice
  rfl

-- dsimp reduces a matcher whose selected alternative binds a constructor field
inductive UnfoldOut where
  | val
  | stuck (n : Nat)

structure UnfoldStore where
  w : Nat
  l : List Nat

def unfoldAmount : Nat → Option Nat
  | 0 => none
  | k + 1 => some k

def unfoldSpendH (_ : UnfoldStore) (n : Nat) : UnfoldOut := .stuck n

def unfoldSpendN (s : UnfoldStore) (x : Nat) : UnfoldOut :=
  match unfoldAmount x with
  | none => .stuck 0
  | some n => match s with | ⟨_, _⟩ => unfoldSpendH s n

theorem unfoldSpendN_nv (s : UnfoldStore) (x : Nat) : unfoldSpendN s x ≠ .val := by
  cases s
  unfold unfoldSpendN
  cases qa : unfoldAmount x
  all_goals dsimp only
  · intro h; cases h
  · intro h; cases h
