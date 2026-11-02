import Examples.ProgramsProofs.InstrumentedInsertionSort

namespace Tutorial

def sortNats (xs : Array Nat) : IO (Array Nat) := pure (insertionSort xs)

def sortStrings (xs : Array String) : IO (Array String) := pure (insertionSort xs)

def sortAndOriginal (xs : Array Nat) : IO (Array Nat × Array Nat) :=
  pure (insertionSort xs, xs)

end Tutorial
