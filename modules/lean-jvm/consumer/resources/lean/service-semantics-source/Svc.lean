namespace Svc
def count (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do acc := acc + i
  pure acc
def pick (xs : Array Nat) (i : Nat) : Nat := xs[i]!
def boom (n : Nat) : Nat := if n == 0 then panic! "zero" else n
def failing (n : Nat) : IO Nat := if n == 0 then throw (IO.userError "zero") else pure n
def loud (n : Nat) : IO Nat := do
  IO.println s!"loud {n}"
  pure (boom n)
end Svc
