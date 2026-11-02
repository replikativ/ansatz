def debugString (x : String) : IO String := pure (dbgTraceIfShared "string" x)
def debugNat (x : Nat) : IO Nat := pure (dbgTraceIfShared "nat" x)

def debugArray (xs : Array Nat) : IO (Array Nat × Array Nat) :=
  pure (dbgTraceIfShared "array" xs, xs)

def debugArrayPure (xs : Array Nat) : Array Nat × Array Nat :=
  (dbgTraceIfShared "array" xs, xs)

def debugBranch (leaf : Bool) (seed : Nat) : IO Nat := do
  if leaf then
    pure (dbgTraceIfShared "leaf" (toString seed)).length
  else
    pure (dbgTraceIfShared "array" (#[seed, seed + 1, seed + 2] : Array Nat)).size
