prelude
import Init.Prelude

def applyNat (f : Nat → Nat) (n : Nat) : Nat := f n
def addBase (k : Nat) : Nat → Nat := fun n => Nat.add k n
def captured (n : Nat) : Nat := applyNat (addBase 7) n
