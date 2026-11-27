/-
Pairs with: ansatz.constructions-test/prop-structure-cases-on-computes-on-opaque-proofs
Observed with Lean v4.36.0 (core only), Meta/Constructions/CasesOn.lean mkCasesOnViaProjs? and
RecOn.lean mkRecOnViaCasesOn?: a one-constructor, index-free, nonrecursive, Prop-valued,
large-eliminating type gets `casesOn` applying the minor to the projections of the major, and
`recOn := casesOn`; both compute on an opaque proof. `Exists` (not large-eliminating) keeps the
recursor-built `casesOn`.
-/
example {p q : Prop} (h : p ∧ q) : And.casesOn (motive := fun _ => Nat) h (fun _ _ => 7) = 7 := rfl
example {p q : Prop} (h : p ∧ q) : And.recOn (motive := fun _ => Nat) h (fun _ _ => 7) = 7 := rfl

structure Both (p q : Prop) : Prop where
  left : p
  right : q

example {p q : Prop} (h : Both p q) : Both.casesOn (motive := fun _ => Nat) h (fun _ _ => 7) = 7 := rfl
example {p q : Prop} (h : Both p q) : Both.recOn (motive := fun _ => Nat) h (fun _ _ => 7) = 7 := rfl
-- the value: the minor applied to the projections; recOn is casesOn
example : @Both.casesOn = fun _ _ _ t mk => mk t.1 t.2 := rfl
example : @Both.recOn = @Both.casesOn := rfl

-- the permutation around `.rec` does not compute on an opaque proof
example {p q : Prop} (h : Both p q) :
    Both.rec (motive := fun _ => Nat) (fun _ _ => 7) h = 7 := by
  fail_if_success rfl
  exact Both.casesOn (motive := fun h => Both.rec (motive := fun _ => Nat) (fun _ _ => 7) h = 7) h (fun _ _ => rfl)

inductive Two : Prop where | mk (a : True) (b : True)
example (h : Two) : Two.casesOn (motive := fun _ => Nat) h (fun _ _ => 3) = 3 := rfl

-- Exists eliminates only into Prop: its casesOn stays the recursor's
/-- info: @Exists.casesOn : ∀ {α : Sort u_1} {p : α → Prop} {motive : Exists p → Prop} (t : Exists p),
  (∀ (w : α) (h : p w), motive ⋯) → motive t -/
#guard_msgs in #check @Exists.casesOn
