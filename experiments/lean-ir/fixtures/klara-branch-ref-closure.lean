import Init

namespace KlaraBranch

-- Lab effects are supplied by the host adapter; no native IO is performed.
@[extern "klara_branch_choose"] opaque choose (ref : @& IO.Ref Nat) (read : @& (Unit → IO Nat)) : IO Nat
@[extern "klara_branch_emit"] opaque emit (value : Nat) : IO Unit

@[noinline] def capturedRead (ref : IO.Ref Nat) (_ : Unit) : IO Nat := ref.get
@[noinline] def invoke (read : Unit → IO Nat) : IO Nat := read ()

-- Both a direct reference owner and its closure alias survive the choose call.
@[noinline] def entry : IO Nat := do
  let ref ← IO.mkRef 0
  let read := capturedRead ref
  let answer ← choose ref read
  ref.set answer
  let observed ← invoke read
  emit observed
  pure observed

end KlaraBranch
