prelude
import Init.Prelude

def increment (n : Nat) : Nat := Nat.add n 1
def incrementTwice (n : Nat) : Nat := increment (increment n)
