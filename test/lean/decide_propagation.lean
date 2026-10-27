import Init

-- Lean/Meta/Tactic/Grind/Propagate.lean: propagateDecideUp/Down.
def decidedEqual (x y : Nat) : Bool := decide (x = y)
example (x y : Nat) (h : x = y) : decidedEqual x y = true := by grind [decidedEqual]
example (x y : Nat) (h : decidedEqual x y = true) : x = y := by grind [decidedEqual]
example (x y : Nat) (h : x ≠ y) : decidedEqual x y = false := by grind [decidedEqual]
example (x y : Nat) (h : decidedEqual x y = false) : x ≠ y := by grind [decidedEqual]

example (s : String) (h0 : s = "a") (h1 : s = "b") : False := by grind
