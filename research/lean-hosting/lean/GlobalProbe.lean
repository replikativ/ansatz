import Init

namespace GlobalProbe
@[noinline] def seed (n : Nat) : Nat := n + 1
@[noinline] def values : List Nat := [seed 40, seed 41]
@[noinline] def readValues (_ : Unit) : List Nat := values
@[noinline] def noncapturing (n : Nat) : Nat := n + 1
@[noinline] def callback (_ : Unit) : Nat → Nat := noncapturing
end GlobalProbe

initialize initializedNat : Nat ← pure 73
@[noinline] def readInitialized (_ : Unit) : Nat := initializedNat

initialize pure ()

initialize initializedWide : UInt64 ← pure 18446744073709551615
@[noinline] def readInitializedWide (_ : Unit) : UInt64 := initializedWide
initialize initializedList : List Nat ← pure GlobalProbe.values
@[noinline] def readInitializedList (_ : Unit) : List Nat := initializedList

def main : IO Unit := do
  IO.println GlobalProbe.values
  IO.println (GlobalProbe.callback () 42)
  IO.println (readInitialized ())
  IO.println (readInitializedWide ())
  IO.println (readInitializedList ())
