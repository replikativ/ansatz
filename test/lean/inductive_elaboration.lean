import Init

inductive Bounded where
  | mk (n : Nat) (h : n ≤ 3)
inductive Flagged : Bool → Type where
  | off : Flagged false
  | on : Flagged true
example (n : Nat) (h : n ≤ 3) : Bounded := Bounded.mk n h
example : Flagged false := Flagged.off
example : Flagged true := Flagged.on

inductive IntBounded where
  | mk (x : Int) (h : x ≤ 3)
example (x : Int) (h : x ≤ 3) : IntBounded := IntBounded.mk x h
inductive InferredField where
  | mk (x : _) (h : x = (x : Nat))
inductive InferredHeader (x : _) (h : x = (x : Nat)) where
  | mk

inductive DepBound (n : Nat) (p : n ≤ 3) where
  | mk (xs : List Nat) (h : some n = some n)
inductive Witnessed : (n : Nat) → n ≤ 3 → Type where
  | mk (n : Nat) (h : n ≤ 3) : Witnessed n h
inductive IndexedElement (A : Type) : A → Type where
  | mk (x : A) : IndexedElement A x
example (A : Type) (x : A) : IndexedElement A x := IndexedElement.mk x
inductive Dependent (A : Type) where
  | mk (x : A) (h : x = x) (d : Decidable (x = x))
example (n : Nat) (h : n ≤ 3) : Witnessed n h := Witnessed.mk n h
example (A : Type) (x : A) (h : x = x) (d : Decidable (x = x)) : Dependent A :=
  Dependent.mk x h d

inductive Shadowed (n : Nat) where
  | mk (n : Nat)
inductive ShadowFamily where
  | mk (ShadowFamily : Nat)
example (outer inner : Nat) : Shadowed outer := @Shadowed.mk outer inner

inductive ImplicitRecursive (A : Type) where
  | nil
  | cons (x : A) (xs : ImplicitRecursive A)
example : ImplicitRecursive Nat := ImplicitRecursive.cons 1 ImplicitRecursive.nil

inductive Counted (A : Type u) : Nat → Type u where
  | nil : Counted A 0
  | cons (x : A) (n : Nat) (xs : Counted A n) : Counted A (n + 1)
inductive Branches where
  | node (children : List Branches)
example (n : Nat) (xs : Counted Nat n) : Counted Nat (n + 1) := Counted.cons 7 n xs
inductive ExprFields where
  | mk (n : Nat)

-- Negative cases are rejected before any declaration is admitted.
example : True := by
  fail_if_success exact (3 : Bool)
  trivial
/--
error: failed to synthesize instance of type class
  OfNat Bool 3
numerals are polymorphic in Lean, but the numeral `3` cannot be used in a context where the expected type is
  Bool
 due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
inductive BadIndex : Bool → Type where
  | mk : BadIndex 3
/--
error: failed to synthesize instance of type class
  OfNat (Sort ?u.3) 3
numerals are polymorphic in Lean, but the numeral `3` cannot be used in a context where the expected type is
  Sort ?u.3
 due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
inductive BadField where
  | mk (h : 3)
/-- error: (kernel) arg #1 of 'Negative.mk' has a non positive occurrence of the datatypes being declared -/
#guard_msgs in
inductive Negative where
  | mk (f : Negative → Nat)

/-- error: (kernel) invalid occurrence of datatype 'Varying' being declared: it must be applied to the parameters and universe levels of the mutual declaration -/
#guard_msgs in
inductive Varying (A : Type) where
  | mk (xs : Varying Nat)

inductive SolvedRecursive (A : Type) : A → Type where
  | leaf (x : A) : SolvedRecursive A x
  | mk (x : A) (xs : SolvedRecursive _ x) : SolvedRecursive A x
example (A : Type) (x : A) (xs : SolvedRecursive A x) : SolvedRecursive A x :=
  SolvedRecursive.mk x xs

/--
error: don't know how to synthesize placeholder for argument `A`
context:
A : Type
x : A
⊢ Type
-/
#guard_msgs in
inductive RecursiveHole (A : Type) where
  | mk (x : A) (xs : RecursiveHole _)
