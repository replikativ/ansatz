prelude
import Init.Prelude

def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)
