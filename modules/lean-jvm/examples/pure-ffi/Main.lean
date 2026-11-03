import Bindings

namespace Interop

initialize initialized : Nat ← pure (normalize 5)

def initialValue (n : Nat) : Nat := initialized + n

def pipeline (n : Nat) : Nat := normalize n + normalize 3

def process (n : Nat) : Message :=
  normalizeMessage { count := n, enabled := true }

def callCombine (n : Nat) : Message := combine n true "abc"

def callConstant (n : Nat) : Nat := constant + n

def mapped (n : Nat) : Nat := ([n, n + 1].map twice).foldl (· + ·) 0

def containsA (s : String) : Bool := s.any isA

end Interop
