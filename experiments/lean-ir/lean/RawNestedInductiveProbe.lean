prelude
unsafe axiom lcAny : Sort 1
unsafe axiom lcErased : Sort 1
unsafe axiom lcVoid : Sort 1
inductive Container (α : Type) : Type where
  | nil
  | cons (head : α) (tail : Container α)
inductive Tree : Type where
  | node (children : Container Tree)
inductive EmptyContainer (α : Type) : Type
inductive SparseTree : Type where
  | node (children : EmptyContainer SparseTree)
inductive MixedTree : Type where
  | leaf
  | node (left : MixedTree) (children : Container MixedTree)
