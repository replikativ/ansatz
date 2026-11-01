prelude
import Init.Prelude

def defaults : List Nat := List.cons 2 (List.cons 3 (List.cons 5 List.nil))
def fallback : Nat := 42
def selected : Nat :=
  match defaults with
  | List.nil => fallback
  | List.cons n _ => n
