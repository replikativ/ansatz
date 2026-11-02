import Lean
set_option linter.unusedVariables false

-- Lean Elab/Tactic/BuiltinTactic.lean evalTraceState, evalCase, evalCase'.
example (n : Nat) : True ∧ True := by
  constructor
  trace_state
  all_goals exact True.intro
example : True := by
  trace_state
  exact True.intro
  trace_state
example (n : Nat) : n = n := by
  cases n
  case' zero => skip
  case zero => rfl
  case succ => rfl
example (b : Bool) : True ∧ True := by
  cases b
  case' true =>
    constructor
    exact True.intro
  case true => exact True.intro
  case false => exact ⟨True.intro, True.intro⟩
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h
  case' inr hq => left
  case inr => exact hq
  case inl hp => exact Or.inr hp
example (b : Bool) : b = b := by
  cases b
  case' true => rfl
  case false => rfl
example (b : Bool) : True ∧ True := by
  cases b
  case' true => constructor
  case true.left => exact True.intro
  case true.right => exact True.intro
  case false => exact ⟨True.intro, True.intro⟩
example (n : Nat) : n = n := by
  cases n
  fail_if_success case zero => skip
  all_goals rfl

-- Lean Elab/Tactic/ElabTerm.lean evalExact and Rewrite.lean elabRewrite.
example (j : Nat) (P : Nat → Prop) (h : P (j + 0)) : P j := by exact h
example (j : Nat) (P : Nat → Prop) (h : P (Nat.add j 0)) : P j := by exact h
example (j : Nat) (P : Nat → Prop) (h : P (Nat.add j Nat.zero)) : P j := by exact h
example (j : Nat) (P : Nat → Prop) (h : P (0 + j)) : P j := by
  fail_if_success exact h
  simpa only [Nat.zero_add] using h
example (j : Nat) (subst : Nat → Nat → Nat → Nat) (v x : Nat)
    (P : Nat → Prop) (h : P (subst (j + 0) v x)) : P (subst j v x) := by exact h
example (j : Nat) (subst : Nat → Nat → Nat → Nat) (v x : Nat)
    (P : Nat → Prop) (tf : ∀ k : Nat, P (subst (j + k) v x)) : P (subst j v x) := by
  exact tf 0
example (n : Nat) : n + 0 = n := by rw [Nat.add_zero _]
example (x y : Nat) : x + y = y + x := by rw [Nat.add_comm _ _]
private theorem carry (x y z : Nat) (h : x = y) : x + z = y + z := by rw [h]
example (x y z : Nat) (h : x = y) : x + z = y + z := by rw [carry _ _ _ h]
example (h : True) : True := by
  have hh := h
  exact hh
