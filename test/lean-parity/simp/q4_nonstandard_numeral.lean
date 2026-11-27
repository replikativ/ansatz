/-
Ansatz test: ansatz.tactic.simp-pre-test/the-literal-shortcut-needs-the-standard-numeral-instances
Observed with Lean v4.36.0: getNatValue?/getIntValue? ignore the instance, so reduceCtorEq treats
`@OfNat.ofNat Nat 1 weird` (weird := ⟨0⟩) as `Nat.succ 0` and `@Neg.neg Int negI 1` as
`Int.negSucc 0`; the proofs it builds are rejected by the kernel. Ansatz deliberately differs:
with a nonstandard instance the shortcut does not fire and the hypothesis is left unchanged.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

instance weird : OfNat Nat (nat_lit 1) := ⟨0⟩
axiom negI : Neg Int

/--
error: No goals to be solved
---
error: (kernel) application type mismatch
  False.elim (noConfusion_of_Nat Nat.ctorIdx h)
argument has type
  Bool.rec False True ((Nat.ctorIdx 1).beq (Nat.ctorIdx 0))
but function has type
  False → False
-/
#guard_msgs in
example (h : @OfNat.ofNat Nat (nat_lit 1) weird = 0) : True := by
  simp only [reduceCtorEq] at h
  trivial

/--
error: No goals to be solved
---
error: (kernel) application type mismatch
  False.elim (noConfusion_of_Nat Int.ctorIdx h)
argument has type
  Bool.rec False True ((-1).ctorIdx.beq (Int.ofNat n).ctorIdx)
but function has type
  False → False
-/
#guard_msgs in
example (n : Nat) (h : @Neg.neg Int negI (1 : Int) = Int.ofNat n) : True := by
  simp only [reduceCtorEq] at h
  trivial
