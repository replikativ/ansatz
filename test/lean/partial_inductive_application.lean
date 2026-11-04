inductive PartialR (roots : List Nat) : Nat → Prop where
  | mk (x : Nat) (h : x ∈ roots) : PartialR roots x

theorem usePred (P : Nat → Prop) (x : Nat) (h : P x) : P x := h

theorem familyExact (roots : List Nat) (x : Nat) (h : PartialR roots x) : PartialR roots x := by
  exact usePred (PartialR roots) x h

theorem familyApply (roots : List Nat) (x : Nat) (h : PartialR roots x) : PartialR roots x := by
  apply usePred (PartialR roots) x
  exact h

theorem familyHave (roots : List Nat) (x : Nat) (h : PartialR roots x) : PartialR roots x := by
  have hx : PartialR roots x := usePred (PartialR roots) x h
  exact hx

def familyBody (roots : List Nat) : Nat → Prop := PartialR roots
example (roots : List Nat) : familyBody roots = (fun x => PartialR roots x) := rfl

structure PartialBox (α : Type) (β : Type) where
  left : α
  right : β

def useType (F : Type → Type) := F Nat
example : useType (PartialBox Nat) = PartialBox Nat Nat := rfl

def useFn (f : Nat → Nat) (x : Nat) := f x
example : useFn (Nat.add 1) 2 = 3 := rfl

def useCons (f : List Nat → List Nat) (xs : List Nat) := f xs
example (xs : List Nat) : useCons (List.cons 1) xs = 1 :: xs := rfl
example (xs : List Nat) : useCons (@List.cons Nat 1) xs = 1 :: xs := rfl
