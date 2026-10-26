import Init

namespace NatRegionProbe

@[noinline] partial def sum (n acc : Nat) : Nat :=
  if n == 0 then acc else sum (n - 1) (acc + n)

@[noinline] def subtract (a b : Nat) : Nat := a - b

@[noinline] def identityNat (n : Nat) : Nat := n

@[noinline] def constantNat (_n : Nat) : Nat := 7

mutual
  @[noinline] partial def bounceA (n acc : Nat) : Nat :=
    if n == 0 then acc else bounceB (n - 1) (acc + n) 3

  @[noinline] partial def bounceB (n acc delta : Nat) : Nat :=
    if n == 0 then acc + delta else bounceA (n - 1) (acc + n + delta)
end

end NatRegionProbe

def main : IO Unit := do
  IO.println s!"sum:{NatRegionProbe.sum 10 0}"
  IO.println s!"sum-promote:{NatRegionProbe.sum 2 9223372036854775807}"
  IO.println s!"subtract-saturate:{NatRegionProbe.subtract 2 7}"
  IO.println s!"subtract:{NatRegionProbe.subtract 7 2}"
  IO.println s!"identity-big:{NatRegionProbe.identityNat 9223372036854775808}"
  IO.println s!"constant:{NatRegionProbe.constantNat 99}"
  IO.println s!"bounceA:{NatRegionProbe.bounceA 3 0}"
  IO.println s!"bounceB:{NatRegionProbe.bounceB 3 0 5}"
