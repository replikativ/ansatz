prelude
import Init.Prelude

@[noinline] def increment (n : Nat) : Nat := n + 1

def incrementTwice (n : Nat) : Nat := increment (increment n)
