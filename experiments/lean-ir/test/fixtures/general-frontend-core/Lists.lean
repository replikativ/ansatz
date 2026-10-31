prelude
import Init.Prelude

def total (xs : List Nat) : Nat :=
  match xs with
  | List.nil => 0
  | List.cons n ns => Nat.add n (total ns)
def listAnswer : Nat := total (List.cons 2 (List.cons 3 (List.cons 5 List.nil)))
