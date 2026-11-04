structure DepAccessor (S : Type) where
  value : S
  witness : value = value
  law : witness = witness

class LawAccessor (S : Type) where
  zero : S
  law : zero = zero

#check DepAccessor.value
#check DepAccessor.witness
set_option pp.proofs true in
#check DepAccessor.law
#check LawAccessor.law
example (s : DepAccessor S) : s.value = s.value := s.witness
example (s : DepAccessor S) : s.witness = s.witness := s.law
example (s : LawAccessor S) : s.zero = s.zero := s.law

structure ChildAccessor (S : Type) extends LawAccessor S where
  other : S
  other_eq : other = zero
#check ChildAccessor.other_eq
example (s : ChildAccessor S) : s.other = s.toLawAccessor.zero := s.other_eq

structure ParamAccessor (S : Type) (x : S) where
  value : S
  law : value = x
#check ParamAccessor.law
example (s : ParamAccessor S x) : s.value = x := s.law

structure ClosedAccessor where
  value : Nat
  law : value = value
#check ClosedAccessor.law
