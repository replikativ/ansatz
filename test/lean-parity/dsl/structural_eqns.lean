/-
Pairs with: ansatz.structural-eqns-test
Observed with Lean v4.36.0 (core only), Elab/PreDefinition/Structural/Eqns.lean: a structural
definition over an indexed family gets `f.eq_1`, `f.eq_2` and `f.eq_def` (proved by exposing the
`.brecOn` application, rewriting with `.brecOn.eq` and splitting the residual matches); the
unfolding equation does not hold by `rfl` on a variable.
-/
inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons {n} (x : α) (xs : V α n) : V α (n+1)

def depth : V α n → Nat
  | .nil => 0
  | .cons _ xs => depth xs + 1
termination_by structural v => v

/-- info: @depth.eq_1 : ∀ {α : Type}, depth V.nil = 0 -/
#guard_msgs in #check @depth.eq_1
/-- info: @depth.eq_2 : ∀ {α : Type} (n_2 : Nat) (x_1 : α) (xs : V α n_2), depth (V.cons x_1 xs) = depth xs + 1 -/
#guard_msgs in #check @depth.eq_2
/--
info: @depth.eq_def : ∀ {α : Type} {n : Nat} (x : V α n),
  depth x =
    match n, x with
    | .(0), V.nil => 0
    | .(n + 1), V.cons x xs => depth xs + 1
-/
#guard_msgs in #check @depth.eq_def

-- the unfolding equation needs a proof: rfl fails on a variable
example {α n} (v : V α n) :
    depth v = (match n, v with | _, .nil => 0 | _, .cons _ xs => depth xs + 1) := by
  fail_if_success rfl
  exact depth.eq_def v
