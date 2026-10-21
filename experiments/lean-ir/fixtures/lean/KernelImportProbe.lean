prelude
axiom A : Sort 1
def aliasA : Sort 1 := A
opaque hiddenA : Sort 1 := A
theorem identityProof : ∀ (p : Prop), p → p := fun p h => h
unsafe def unsafeA : Sort 1 := A
inductive Tiny : Type where
  | mk
universe u
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
init_quot
