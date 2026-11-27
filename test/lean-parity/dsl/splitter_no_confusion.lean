/-
Pairs with: ansatz.tactic.match-eqns-test (splitter simplification of constructor equations)
Observed with Lean v4.36.0 (core only), the facts AppBuilder.mkNoConfusion relies on and the
splitter's equation simplification must follow:
- `ctorIdx` of an indexed family takes the indices too (`@D.ctorIdx Nat` alone is rejected);
- the per-constructor `noConfusion` of an indexed family takes `HEq` for the major equality, so a
  homogeneous `h : D.a x = D.a y` goes through `heq_of_eq h`;
- its continuation receives only the data-field equalities: a proof field contributes none;
- a match on an indexed family gets equation lemmas whose proofs need these.
-/
inductive D (α : Type) : Nat → Type where
  | a (x : α) : D α (n+1)
  | b (x : α) (y : α) : D α (n+1)

/-- info: @D.ctorIdx : {α : Type} → {a : Nat} → D α a → Nat -/
#guard_msgs in #check @D.ctorIdx

/--
error: Type mismatch
  @D.ctorIdx Nat
has type
  {a : Nat} → D Nat a → Nat
but is expected to have type
  D Nat 1 → Nat
-/
#guard_msgs in example : D Nat 1 → Nat := (@D.ctorIdx Nat : {a : Nat} → D Nat a → Nat)

/--
info: @D.a.noConfusion : {α : Type} →
  {P : Sort u_1} →
    {n : Nat} → {x : α} → {n' : Nat} → {x' : α} → n + 1 = n' + 1 → D.a x ≍ D.a x' → (n = n' → x ≍ x' → P) → P
-/
#guard_msgs in #check @D.a.noConfusion

-- the index equality, then `heq_of_eq h`; the homogeneous `h` is rejected
example (x y : Nat) (h : (D.a x : D Nat 1) = D.a y) : x = y := by
  fail_if_success exact D.a.noConfusion rfl h (fun _ e => eq_of_heq e)
  exact D.a.noConfusion rfl (heq_of_eq h) (fun _ e => eq_of_heq e)

-- different constructors: noConfusion_of_Nat over ctorIdx applied to the indices
example (x y z : Nat) (h : (D.a x : D Nat 1) = D.b y z) : False :=
  noConfusion_of_Nat (@D.ctorIdx Nat 1) h

-- a proof field contributes no equality to the continuation
inductive P where
  | mk (n : Nat) (h : n > 0) : P
/--
info: @P.mk.noConfusion : {P : Sort u_1} →
  {n : Nat} → {h : n > 0} → {n' : Nat} → {h' : n' > 0} → _root_.P.mk n h = _root_.P.mk n' h' → (n = n' → P) → P
-/
#guard_msgs in #check @P.mk.noConfusion

-- a match on the indexed family: Lean's equation lemma for the second branch is proved
def tag : D Nat (n+1) → Nat
  | .a _ => 0
  | .b x _ => x
/-- info: tag.eq_2 {n : Nat} (x_1 y : Nat) : tag (D.b x_1 y) = x_1 -/
#guard_msgs in #check tag.eq_2
