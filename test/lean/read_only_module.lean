-- Lean/Environment.lean: readModuleData loads existing declarations without saving.
import Init
example (n : Nat) : n = n := by rfl
