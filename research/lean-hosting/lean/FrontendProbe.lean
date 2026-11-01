import Init

namespace FrontendProbe

syntax "keepValue " term : term
macro_rules
  | `(keepValue $x) => `((fun y => y) $x)

@[extern "ansatz_host_transform"] opaque hostTransform : Nat → Nat
@[noinline] def answer (x : Nat) : Nat := hostTransform (keepValue x)

end FrontendProbe
