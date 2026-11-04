import Lean
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

example (h : True) : True := by
  fail_if_success simp [no_such_lemma]
  fail_if_success simp only [no_such_lemma]
  fail_if_success simp_all [no_such_lemma]
  fail_if_success simp_all only [no_such_lemma]
  fail_if_success dsimp [no_such_lemma]
  fail_if_success dsimp only [no_such_lemma]
  fail_if_success dsimp [no_such_lemma] at h
  fail_if_success dsimp only [no_such_lemma] at h
  fail_if_success simp [no_such_lemma] at h
  fail_if_success simp only [no_such_lemma] at h
  exact h
example (n : Nat) : n = n := by
  simp only [Nat.add_zero]
example (n : Nat) : n = n := by
  simp only [Nat.add_eq]
example (n : Nat) : n = n := by
  simp only [Nat.le_eq]
example (n : Nat) : n = n := by
  simp only [Nat.reduceEqDiff]
example (n : Nat) : n = n := by
  dsimp only [Nat.reduceEqDiff]
example (n : Nat) : n = n := by
  simp only [Char.reduceToNat]
example (n : Nat) : n = n := by
  dsimp only [Char.reduceToNat]

-- Positive resolution pairs from every module contributing builtin registrations.
-- Construct identifiers from the registered Names to preserve private/macro scopes.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let registry ← Meta.Simp.builtinSimprocDeclsRef.get
  let names := registry.keys.toList.map Prod.fst
  let mut modules : Std.HashSet Name := {}
  for n in names do
    let some idx := env.getModuleIdxFor? n | throwError "missing simproc module"
    let mod := env.header.moduleNames[idx]!
    if modules.contains mod then continue
    modules := modules.insert mod
    elabCommand (← `(example (x : Nat) : x = x := by simp only [$(mkIdent n):ident]))
    elabCommand (← `(example (x : Nat) : x = x := by dsimp only [$(mkIdent n):ident]))
  unless modules.size == 21 do throwError "expected 21 builtin simproc modules"

-- Argument errors precede a location that would otherwise close the goal.
example (P : Prop) (h : False) (k : True) : P := by
  fail_if_success simp [no_such_lemma] at h k ⊢
  fail_if_success simp only [no_such_lemma] at *
  fail_if_success dsimp [no_such_lemma] at h k ⊢
  fail_if_success dsimp only [no_such_lemma] at *
  fail_if_success simp_all [no_such_lemma]
  fail_if_success simp_all only [no_such_lemma]
  exact False.elim h
example (P : Prop) (h : False) (k : True) : P := by
  simp only [Nat.reduceEqDiff] at h k ⊢
example (P : Prop) (h : False) (k : True) : P := by
  dsimp only [Char.reduceToNat] at h k ⊢
example (P : Prop) (h : False) : P := by
  simp only [Nat.reduceEqDiff] at *
example (P : Prop) (h : False) : P := by
  dsimp only [Char.reduceToNat] at *
