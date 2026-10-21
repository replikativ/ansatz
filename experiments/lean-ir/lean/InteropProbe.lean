import Init

namespace InteropProbe

@[extern "ansatz_host_transform"] opaque hostTransform : Nat → Nat
@[extern "ansatz_host_apply"] opaque hostApply : (Nat → Nat) → Nat → Nat

@[noinline] def identity (x : Nat) : Nat := x
@[noinline] def callHost (x : Nat) : Nat := hostTransform x
@[noinline] def roundTrip (x : Nat) : Nat := hostApply (fun _ => x) x
@[noinline] def applyCallback (f : Nat → Nat) (x : Nat) : Nat := f x

end InteropProbe
