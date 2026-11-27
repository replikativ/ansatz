/-
Pairs with: ansatz.structure-extends-test/extends-applied-parent
Observed with Lean v4.36.0 (core only):
- `Child α extends Parent (List α)`: the inherited field is `Parent.x` of the subobject, whose type
  is `Parent (List α)`, so `c.x : List α`;
- a child field whose type binds a name equal to a parent field (`∀ x : Nat, x = x`) keeps its
  own bound variable: the parent field is in scope only where it is not shadowed;
- an unshadowed reference to the parent field in a child field type is the subobject's field.
-/
structure Parent (β : Type) where
  x : β

structure Child (α : Type) extends Parent (List α) where
  law : ∀ x : Nat, x = x
  nonempty : x ≠ []

/-- info: Child.toParent {α : Type} (self : Child α) : Parent (List α) -/
#guard_msgs in #check Child.toParent

example (c : Child Nat) : c.x = c.toParent.x := rfl
example (c : Child Nat) : (c.x : List Nat) = c.x := rfl

/-- info: Child.law {α : Type} (self : Child α) (x : Nat) : x = x -/
#guard_msgs in #check Child.law
/-- info: Child.nonempty {α : Type} (self : Child α) : self.x ≠ [] -/
#guard_msgs in #check Child.nonempty

example : Child Nat := { x := [1], law := fun _ => rfl, nonempty := by simp }
