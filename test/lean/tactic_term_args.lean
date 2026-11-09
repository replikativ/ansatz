-- Lean 4.33.1: `apply`/`exact`/`refine` take one term, and `apply f a b` parses as
-- `apply (f a b)`. A failing tactic reports the goal it ran on.
-- test/ansatz/tactic/tactic_errors_test.clj mirrors these. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/tactic_term_args.lean

example (a b : Nat) (h : a < b) : a ≤ b := by apply Nat.le_of_lt h
example (a b : Nat) (h : a < b) : a ≤ b := by exact Nat.le_of_lt h
example (a b : Nat) (h : a < b) : a ≤ b := by refine Nat.le_of_lt h

/--
error: Type mismatch
  h
has type
  a < b
but is expected to have type
  a ≤ b
-/
#guard_msgs in
example (a b : Nat) (h : a < b) : a ≤ b := by exact h
