/-
Pairs with: ansatz.binder-kinds-test
Observed with Lean v4.36.0 (core only), Elab/MutualInductive.lean / Elab/Inductive.lean:
- header binder kinds survive in the type former and, with explicit parameters turned implicit
  (withExplicitToImplicit), in the constructors; instance and strict-implicit binders survive;
- a constructor field keeps its binder kind; the recursor, casesOn and recOn take the
  parameters and the outer indices implicitly and show each field's kind in the minor premise;
- a fixed prefix of indices is promoted to parameters (`Fix` has one parameter), unless
  `inductive.autoPromoteIndices` is off.
-/
inductive Fam {α : Type} [Inhabited α] : Nat → Type where
  | mk ⦃x : α⦄ (n : Nat) : Fam n
/-- info: @Fam : {α : Type} → [Inhabited α] → Nat → Type -/
#guard_msgs in #check @Fam
/-- info: @Fam.mk : {α : Type} → [inst : Inhabited α] → ⦃x : α⦄ → (n : Nat) → Fam n -/
#guard_msgs in #check @Fam.mk
/--
info: @Fam.casesOn : {α : Type} →
  [inst : Inhabited α] →
    {motive : (a : Nat) → Fam a → Sort u_1} →
      {a : Nat} → (t : Fam a) → (⦃x : α⦄ → (n : Nat) → motive n (Fam.mk n)) → motive a t
-/
#guard_msgs in #check @Fam.casesOn

inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons {n} (x : α) (xs : V α n) : V α (n+1)
/-- info: @V.cons : {α : Type} → {n : Nat} → α → V α n → V α (n + 1) -/
#guard_msgs in #check @V.cons
/--
info: @V.casesOn : {α : Type} →
  {motive : (a : Nat) → V α a → Sort u_1} →
    {a : Nat} →
      (t : V α a) → motive 0 V.nil → ({n : Nat} → (x : α) → (xs : V α n) → motive (n + 1) (V.cons x xs)) → motive a t
-/
#guard_msgs in #check @V.casesOn

-- index promotion: the index is fixed in every constructor, so it becomes a parameter
inductive Fix : Type u → Type u where
  | wrap (α : Type u) (a : α) : Fix α
/-- info: @Fix.rec : {a : Type u_2} → {motive : Fix a → Sort u_1} → ((a_1 : a) → motive (Fix.wrap a a_1)) → (t : Fix a) → motive t -/
#guard_msgs in #check @Fix.rec
/-- info: Fix.wrap : (α : Type u_1) → α → Fix α -/
#guard_msgs in #check @Fix.wrap

-- promotion happens before universe inference: the promoted index is no field, so `mk` has
-- no proof field and the type is not a Prop candidate
inductive PI (p : Prop) : p → Type where | mk (h : p) : PI p h
/-- info: PI (p : Prop) : p → Type -/
#guard_msgs in #check PI
