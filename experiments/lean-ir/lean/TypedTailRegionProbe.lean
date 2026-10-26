import Init

namespace TypedTailRegionProbe

mutual
@[noinline] partial def bounceA (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else bounceB (n - 1) (acc + n) 1

@[noinline] partial def bounceB (n acc extra : UInt64) : UInt64 :=
  if n == 0 then acc else bounceA (n - 1) (acc + extra)
end

@[noinline] def nested (x y : UInt64) : UInt64 :=
  if x == 0 then
    if y == 0 then 7 else y - 1
  else x + y

@[noinline] def identity64 (x : UInt64) : UInt64 := x
@[noinline] def constant64 (_x : UInt64) : UInt64 := 7
@[noinline] def terminalAdd (x y : UInt64) : UInt64 := x + y
@[noinline] def terminalEq (x y : UInt64) : Bool := x == y

end TypedTailRegionProbe

def main : IO Unit := do
  IO.println s!"bounceA:{TypedTailRegionProbe.bounceA 10 0}"
  IO.println s!"bounceB:{TypedTailRegionProbe.bounceB 10 0 3}"
  IO.println s!"nested-zero:{TypedTailRegionProbe.nested 0 0}"
  IO.println s!"nested-right:{TypedTailRegionProbe.nested 0 9}"
  IO.println s!"nested-add:{TypedTailRegionProbe.nested 2 3}"
  IO.println s!"identity:{TypedTailRegionProbe.identity64 18446744073709551615}"
  IO.println s!"constant:{TypedTailRegionProbe.constant64 123}"
  IO.println s!"add-wrap:{TypedTailRegionProbe.terminalAdd 18446744073709551615 1}"
  IO.println s!"equal:{if TypedTailRegionProbe.terminalEq 18446744073709551615 18446744073709551615 then 1 else 0}"
