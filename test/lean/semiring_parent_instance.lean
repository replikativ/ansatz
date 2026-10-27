import Init

-- Lean v4.33.1: Elab/Structure.lean:addParentInstances registers the parent projection.
class WAddMonoid (S : Type) where
  add : S → S → S
  zero : S
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a

class WSemiring (S : Type) extends WAddMonoid S where
  mul : S → S → S
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_zero : ∀ a, mul a zero = zero
  zero_mul : ∀ a, mul zero a = zero

def wsum {S : Type} [m : WAddMonoid S] : List S → S
  | [] => m.zero
  | x :: xs => m.add x (wsum xs)

example {S : Type} [m : WSemiring S] :
    (inferInstance : WAddMonoid S) = m.toWAddMonoid := rfl

example (X : Type) {S : Type} [m : WSemiring S] (b : S) (f : X → S) (xs : List X) :
    wsum (xs.map (fun x => m.mul b (f x))) = m.mul b (wsum (xs.map f)) := by
  induction xs with
  | nil => simp [wsum, m.mul_zero]
  | cons x xs ih => simp [wsum, ih, m.mul_add]
