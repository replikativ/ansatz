def debugString (x : String) : IO String := pure (dbgTraceIfShared "string" x)
def debugNat (x : Nat) : IO Nat := pure (dbgTraceIfShared "nat" x)

def debugArray (xs : Array Nat) : IO (Array Nat × Array Nat) :=
  pure (dbgTraceIfShared "array" xs, xs)

def debugArrayPure (xs : Array Nat) : Array Nat × Array Nat :=
  (dbgTraceIfShared "array" xs, xs)
