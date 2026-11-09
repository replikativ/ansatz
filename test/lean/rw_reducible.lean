-- Lean 4.33.1: rw's kabstract runs at TransparencyMode.reducible (Init/Meta/Defs.lean
-- Rewrite.Config). `instNatCastInt` is instance-reducible, so the pattern `↑?n` does not
-- match `Int.ofNat a`; it matches the coercion `↑a`.
-- test/ansatz/tactic/rw_reducible_test.clj mirrors these. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/rw_reducible.lean

example (a b : Nat) (h : (a : Int) < (b : Int)) : a < b := by rw [Int.ofNat_lt] at h; exact h

/-- error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  @LT.lt Int Int.instLTInt ↑?m.6 ↑?m.7
in the target expression
  @LT.lt Int Int.instLTInt (Int.ofNat a) (Int.ofNat b)

a b : Nat
h : Int.ofNat a < Int.ofNat b
⊢ a < b -/
#guard_msgs (error) in
example (a b : Nat) (h : Int.ofNat a < Int.ofNat b) : a < b := by rw [Int.ofNat_lt] at h; exact h
