-- Lean 4 reference (checked with lean-lsp lean_run_code on 2026-10-26, Lean v4.33.x): every theorem
-- below is accepted. The ansatz tests in memory_model_probe_test.clj state the same definitions and
-- theorems; ansatz should accept them with the analogous tactic scripts.
structure Own where
  ent : Nat
  scope : Nat

structure St where
  open_ : List Nat
  owns : List Own

def memq (x : Nat) : List Nat → Bool
  | [] => false
  | h :: t => if Nat.beq x h then true else memq x t

def ownersOpen : List Own → List Nat → Bool
  | [], _ => true
  | o :: t, op => if memq o.scope op then ownersOpen t op else false

def inv (s : St) : Bool := ownersOpen s.owns s.open_

def dropOwned (sc : Nat) : List Own → List Own
  | [] => []
  | o :: t => if Nat.beq o.scope sc then dropOwned sc t else o :: dropOwned sc t

def dropNat (x : Nat) : List Nat → List Nat
  | [] => []
  | h :: t => if Nat.beq h x then dropNat x t else h :: dropNat x t

def close (sc : Nat) (s : St) : St := ⟨dropNat sc s.open_, dropOwned sc s.owns⟩

-- T1: closed instance; decide AND rfl both work in Lean
theorem conc_decide : inv (close 2 ⟨[1, 2], [⟨7, 1⟩, ⟨8, 2⟩]⟩) = true := by decide
theorem conc_rfl    : inv (close 2 ⟨[1, 2], [⟨7, 1⟩, ⟨8, 2⟩]⟩) = true := rfl

-- T5/T6: the "3-line lemma" and the preservation theorem, one-liners with grind
theorem memq_drop_grind (x sc : Nat) (op : List Nat) :
    memq x op = true → Nat.beq x sc = false → memq x (dropNat sc op) = true := by
  induction op <;> grind [memq, dropNat, Nat.beq_eq]

theorem close_pres_grind (sc : Nat) (op : List Nat) (os : List Own) :
    ownersOpen os op = true → ownersOpen (dropOwned sc os) (dropNat sc op) = true := by
  induction os <;> grind [ownersOpen, dropOwned, Nat.beq_eq, memq_drop_grind]

-- Same theorems with manual tactics (no grind)
theorem memq_drop (x sc : Nat) (op : List Nat) :
    memq x op = true → Nat.beq x sc = false → memq x (dropNat sc op) = true := by
  induction op with
  | nil => simp [memq]
  | cons h t ih =>
    intro hm hne
    cases hh : Nat.beq h sc <;> cases hx : Nat.beq x h <;> simp_all [memq, dropNat, Nat.beq_eq]

theorem close_pres (sc : Nat) (op : List Nat) (os : List Own) :
    ownersOpen os op = true → ownersOpen (dropOwned sc os) (dropNat sc op) = true := by
  induction os with
  | nil => intro _; simp [dropOwned, ownersOpen]
  | cons o t ih =>
    intro h
    cases hm : memq o.scope op <;> cases hs : Nat.beq o.scope sc <;>
      simp_all [ownersOpen, dropOwned, memq_drop]

-- T2: hypothesis stated as a binder BEFORE induction; Lean's `induction` reverts and
-- re-introduces it, so the IH is generalized over the tail.
theorem close_pres_hyp (sc : Nat) (op : List Nat) (os : List Own)
    (h : ownersOpen os op = true) : ownersOpen (dropOwned sc os) (dropNat sc op) = true := by
  induction os <;> grind [ownersOpen, dropOwned, Nat.beq_eq, memq_drop_grind]

theorem inv_close (sc : Nat) (s : St) : inv s = true → inv (close sc s) = true :=
  close_pres sc s.open_ s.owns
