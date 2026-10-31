prelude
import Init.Prelude

def triangular (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ k => Nat.add (triangular k) (Nat.succ k)
