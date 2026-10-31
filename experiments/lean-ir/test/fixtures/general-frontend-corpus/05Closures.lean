prelude
import Init.Prelude

@[noinline] def applyNat (f : Nat → Nat) (n : Nat) : Nat := f n

@[noinline] def addBase (k : Nat) : Nat → Nat := fun n => k + n

def captured (n : Nat) : Nat := applyNat (addBase 7) n
