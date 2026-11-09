-- Lean 4.33.1 omega (Elab/Tactic/Omega/Frontend.lean handleNatCast): ↑(Int.toNat x) and
-- ↑(Int.natAbs x) are split via Int.toNat_eq_max and Lean.Omega.Int.ofNat_natAbs.
-- test/ansatz/tactic/omega_cast_split_test.clj mirrors these. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/omega_cast_split.lean

example (x : Int) (h : 0 ≤ x) : ((Int.natAbs x : Nat) : Int) = x := by omega
example (x : Int) (h : 0 ≤ x) : ((Int.toNat x : Nat) : Int) = x := by omega
example (x : Int) : 0 ≤ ((Int.toNat x : Nat) : Int) := by omega
example (x : Int) (h : x < 0) : Int.toNat x = 0 := by omega
example (x : Int) (h : x < 0) : ((Int.natAbs x : Nat) : Int) = -x := by omega
example (x : Int) : x ≤ ((Int.natAbs x : Nat) : Int) := by omega
example (x y : Int) : ((Int.natAbs (x + y) : Nat) : Int) ≤ (Int.natAbs x : Int) + (Int.natAbs y : Int) := by omega
