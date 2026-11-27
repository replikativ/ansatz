/-
Pairs with: ansatz.injectivity-test
Observed with Lean v4.36.0 (core only), Meta/Injective.lean:
- every constructor with fields gets `C.inj` (all binders implicit, `C … = C … → eqs`) and
  `C.injEq` (`(C … = C …) = eqs`, the constructor's binder kinds, the new fields explicit);
- a field occurring in the result type (a fixed index such as `n` in `V.cons`) is shared, not
  equated; proof fields contribute no equation; a field whose type differs gets `HEq`;
- a constructor whose fields are all shared or proofs has neither; `.injEq` is a simp lemma.
-/
inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons {n} (x : α) (xs : V α n) : V α (n+1)
/--
info: @V.cons.inj : ∀ {α : Type} {n : Nat} {x : α} {xs : V α n} {x_1 : α} {xs_1 : V α n},
  V.cons x xs = V.cons x_1 xs_1 → x = x_1 ∧ xs = xs_1
-/
#guard_msgs in #check @V.cons.inj
/--
info: @V.cons.injEq : ∀ {α : Type} {n : Nat} (x : α) (xs : V α n) (x_1 : α) (xs_1 : V α n),
  (V.cons x xs = V.cons x_1 xs_1) = (x = x_1 ∧ xs = xs_1)
-/
#guard_msgs in #check @V.cons.injEq

structure Pos where
  n : Nat
  h : 0 < n
/--
info: Pos.mk.injEq : ∀ (n : Nat) (h : 0 < n) (n_1 : Nat) (h_1 : 0 < n_1),
  ({ n := n, h := h } = { n := n_1, h := h_1 }) = (n = n_1)
-/
#guard_msgs in #check @Pos.mk.injEq

inductive T where | a (x : Nat) (y : Bool) | b
/-- info: T.a.injEq : ∀ (x : Nat) (y : Bool) (x_1 : Nat) (y_1 : Bool), (T.a x y = T.a x_1 y_1) = (x = x_1 ∧ y = y_1) -/
#guard_msgs in #check @T.a.injEq
example (x y : Nat) (b c : Bool) (h : T.a x b = T.a y c) : x = y := by simp at h; exact h.1

inductive S where | mk (n : Nat) (f : Fin n)
/-- info: S.mk.injEq : ∀ (n : Nat) (f : Fin n) (n_1 : Nat) (f_1 : Fin n_1), (S.mk n f = S.mk n_1 f_1) = (n = n_1 ∧ f ≍ f_1) -/
#guard_msgs in #check @S.mk.injEq

-- only proofs: no injectivity theorems
inductive OnlyProof where | mk (h : True)
/-- error: Unknown constant `OnlyProof.mk.inj` -/
#guard_msgs in #check @OnlyProof.mk.inj

-- a default value is not part of the field's type (elimOptParam): only the index field is shared
inductive D : Nat → Type where
  | mk (n : Nat) (i : optParam Nat n) : D (Nat.succ i)
/-- info: D.mk.injEq : ∀ (n i n_1 : Nat), (D.mk n i = D.mk n_1 i) = (n = n_1) -/
#guard_msgs in #check @D.mk.injEq
