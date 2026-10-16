import Init

namespace HeapProbe

inductive Tree where
  | leaf (value : Nat)
  | branch (left right : Tree)
  deriving Repr, BEq

@[noinline] def mirror : Tree → Tree
  | .leaf value => .leaf value
  | .branch left right => .branch (mirror right) (mirror left)

end HeapProbe
