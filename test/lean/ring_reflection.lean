import Lean
import Init.Grind.Ring.CommSemiringAdapter
import Init.GrindInstances.Ring.Nat
import Init.GrindInstances.Ring.Int

example (a b c x : Nat) : a + (x * b + (x * x) * c) = a + x * (b + x * c) := by grind
example (x : Nat) : x + x = 2 * x := by grind
example (x y : Nat) : (x + y) * (x + y) = x ^ 2 + 2 * (x * y) + y ^ 2 := by grind
example (x y : Nat) : (x - y) + x = x + (x - y) := by grind
example (x y : Int) : (x + y) * (x + -y) = x * x + -(y * y) := by grind
example (R : Type) [Lean.Grind.CommSemiring R] (x y z : R) :
    x * (y + z) = x * y + x * z := by grind
example (R : Type) [Lean.Grind.CommRing R] (x y z : R) :
    x * (y + -z) = x * y + -(x * z) := by grind
universe u v
example (R : Type (max u v)) [Lean.Grind.CommSemiring R] (x y : R) :
    x + y = y + x := by grind
