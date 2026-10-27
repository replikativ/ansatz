-- Lean src/kernel/environment.cpp check_name rejects redefinition.
def verifiedFunction : Nat := 0
theorem verifiedTheorem : verifiedFunction = 0 := rfl

/-- error: `verifiedFunction` has already been declared -/
#guard_msgs in
def verifiedFunction : Nat := 1

example : verifiedFunction = 0 := rfl
example : verifiedFunction = 0 := verifiedTheorem

/-- error: `verifiedTheorem` has already been declared -/
#guard_msgs in
theorem verifiedTheorem : verifiedFunction = 0 := rfl

example : verifiedFunction = 0 := verifiedTheorem
