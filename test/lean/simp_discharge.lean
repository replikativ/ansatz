import Init

-- Lean/Meta/Tactic/Simp/Rewrite.lean: tryTheoremCore, synthesizeArgs,
-- dischargeUsingAssumption? and dischargeDefault? (checkout 55f80e10a3).
-- `dec` occurs only inside the composite BEq instance in the rule's LHS.
example (K : Type) (dec : DecidableEq K) (x y : K) (hne : ¬(x = y))
    (rule : ∀ (K : Type) (dec : DecidableEq K) (x y : K),
      x ≠ y → @BEq.beq K (@instBEqOfDecidableEq K dec) x y = false) :
    @BEq.beq K (@instBEqOfDecidableEq K dec) x y = false := by
  simp (disch := assumption) only [rule]

-- Init/Data/Nat/Basic.lean: add_eq/le_eq; definitional rewrites count as progress.
example (x y : Nat) : Nat.add x y = Nat.add y x := by
  simp only [Nat.add_eq]
  omega

example (x y z : Nat) (h : Nat.le x y) (k : Nat.le y z) : Nat.le x z := by
  simp only [Nat.le_eq] at h k ⊢
  omega
