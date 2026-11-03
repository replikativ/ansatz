set_option linter.unusedVariables false

-- Lean/LocalContext.lean findFromUserName?; Meta/Tactic/Split.lean withEqs.
example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : 0 = 0) : 1 = 1 → 1 = 1 := by
  intro h
  exact h

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : False) : True → False := by
  intro h
  clear h
  exact h

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : False) : True → True := by
  intro h
  revert h
  intro e
  exact e

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : True) (x : Nat) : x = 1 → x = 1 := by
  intro h
  subst h
  rfl

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : True) : True ∧ False → False := by
  intro h
  cases h
  rename_i ht hf
  exact hf

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : True) (x : Nat) (eqx : x = 1) : x = 2 → 1 = 2 := by
  intro h
  rw [eqx] at h
  exact h

example (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h : True) (x : Nat) : x + 0 = 1 → x = 1 := by
  intro h
  simp only [Nat.add_zero] at h
  exact h

def splitName (n : Nat) : Nat := match n == 3 with | true => 0 | false => n

example (n : Nat) : splitName n ≤ splitName n := by
  simp only [splitName]
  split
  all_goals
    fail_if_success revert h
    fail_if_success revert heq
    rename_i heq
    revert heq
    intro e
    omega

example (p : Prop) [Decidable p] : (if p then 0 else 1) ≤ 1 := by
  split
  all_goals
    fail_if_success revert h
    rename_i h
    omega

example (b : Bool) : b = false ∨ b = true := by
  have hh : (if b then 0 else 1) = (if b then 0 else 1) := rfl
  split at hh
  · rename_i h
    right
    simpa using h
  · next h =>
      left
      cases b <;> simp_all

def scopeMatch (o : Option Nat) : Nat := match o with | none => 0 | some x => x
example (o : Option Nat) : scopeMatch o = scopeMatch o := by
  unfold scopeMatch
  split
  all_goals
    fail_if_success revert x
    rfl

def scopeEqMatch (n : Nat) : Nat :=
  match n with | Nat.succ Nat.zero => 10 | Nat.succ k => k | Nat.zero => 20
example (n : Nat) (f : Nat → Nat) : scopeEqMatch (Nat.succ (f n)) = scopeEqMatch (Nat.succ (f n)) := by
  unfold scopeEqMatch
  split
  all_goals
    fail_if_success revert h
    rfl

example (h : True ∧ False) : False := by
  rcases h with ⟨ht, _⟩
  rename_i hf
  exact hf

example (n : Nat) : n = n → True := by
  intro
  cases n
  all_goals
    rename_i eqn
    trivial

example (n : Nat) : n = n → True := by
  intro
  induction n
  all_goals
    rename_i eqn
    trivial

example (n m : Nat) (eqn : n = m) : n = n → True := by
  intro
  cases eqn
  rename_i hidden
  trivial

example (n m : Nat) (eqn : n = m) : n = n → True := by
  intro
  subst eqn
  rename_i hidden
  trivial

example (p : Prop) (d : Decidable p) (h : False) : @ite Nat p d 0 1 = 0 := by
  split
  all_goals
    rename_i condition
    cases h

/--
error: too many variable names provided
---
error: too many variable names provided
-/
#guard_msgs in
example (p : Prop) (d : Decidable p) (h : False) : @ite Nat p d 0 1 = 0 := by
  split
  all_goals
    rename_i old new
    cases h

example (b : Bool) : (match b with | false => 0 | true => 1) = 0 → True := by
  intro
  split at *
  all_goals
    rename_i eqn
    trivial
