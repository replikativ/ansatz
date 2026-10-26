import Init

namespace ScalarWrapperProbe

@[noinline] partial def sum64 (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else sum64 (n - 1) (acc + n)

@[noinline] partial def sumSize (n acc : USize) : USize :=
  if n == 0 then acc else sumSize (n - 1) (acc + n)

end ScalarWrapperProbe

def main : IO Unit := do
  IO.println s!"uint64:{ScalarWrapperProbe.sum64 10 0}"
  IO.println s!"usize:{ScalarWrapperProbe.sumSize 10 0}"
  IO.println s!"uint64-wrap:{ScalarWrapperProbe.sum64 2 18446744073709551615}"
  IO.println s!"usize-wrap:{ScalarWrapperProbe.sumSize 2 18446744073709551615}"
