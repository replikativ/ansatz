prelude
import Init.Prelude

def total : List Nat → Nat
  | [] => 0
  | n :: ns => n + total ns

def listAnswer : Nat := total [2, 3, 5]
