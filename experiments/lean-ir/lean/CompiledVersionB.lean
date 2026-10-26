import Init

namespace CompiledVersionProbe

@[noinline] partial def sum64 (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else sum64 (n - 1) (acc + n + 1)

@[noinline] def entry (n acc : UInt64) : UInt64 := sum64 n acc
@[noinline] def identity64 (x : UInt64) : UInt64 := x

-- The export records this exact external ABI. The stock interpreter cannot run
-- this local alias without a native object; main uses ordinary arithmetic as a
-- separately labeled source-value oracle, not evidence of this alias FFI route.
@[extern "lean_uint64_sub"] def chosenOp (x y : UInt64) : UInt64 := x - y
@[noinline] def externCall (x y : UInt64) : UInt64 := chosenOp x y

end CompiledVersionProbe

def main : IO Unit := do
  IO.println s!"sum:{CompiledVersionProbe.sum64 10 0}"
  IO.println s!"entry:{CompiledVersionProbe.entry 10 0}"
  IO.println s!"identity:{CompiledVersionProbe.identity64 18446744073709551615}"
  IO.println s!"operation-source-oracle:{(9 : UInt64) - (4 : UInt64)}"
