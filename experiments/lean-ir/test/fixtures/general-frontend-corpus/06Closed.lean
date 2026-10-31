prelude
import Init.Prelude

def defaults : List Nat := [2, 3, 5]

def fallback : Nat := 42

def selected : Nat :=
  match defaults with
  | [] => fallback
  | n :: _ => n
