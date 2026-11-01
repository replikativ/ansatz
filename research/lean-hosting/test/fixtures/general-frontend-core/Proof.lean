prelude
import Init.Prelude

def projectFirst (n : Nat) : Nat := n
theorem projectFirst_eq (n : Nat) : Eq (projectFirst n) n := Eq.refl n
