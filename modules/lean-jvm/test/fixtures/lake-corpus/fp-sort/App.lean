import Examples.ProgramsProofs.InstrumentedInsertionSort
namespace LakeTutorial

def sortNats (xs : Array Nat) : IO (Array Nat) := pure (insertionSort xs)
def sortAndOriginal (xs : Array Nat) : IO (Array Nat × Array Nat) := pure (insertionSort xs, xs)
end LakeTutorial
