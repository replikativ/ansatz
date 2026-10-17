prelude
unsafe axiom lcAny : Sort 1
unsafe axiom lcErased : Sort 1
unsafe axiom lcVoid : Sort 1
inductive TinyEnum : Type where
  | a | b
inductive EmptyType : Type
inductive EmptyProp : Prop
inductive UnitProp : Prop where
  | intro
inductive MyNat : Type where
  | zero
  | succ (n : MyNat)
inductive AtZero : MyNat → Type where
  | zero : AtZero MyNat.zero
mutual
inductive Even : Type where
  | zero
  | next (odd : Odd)
inductive Odd : Type where
  | next (even : Even)
end
universe u
inductive PolyList (α : Type u) : Type u where
  | nil
  | cons (head : α) (tail : PolyList α)
inductive FunctionalTree : Type where
  | node (children : MyNat → FunctionalTree)
inductive SmallEq {α : Sort u} (a : α) : α → Prop where
  | refl : SmallEq a a
