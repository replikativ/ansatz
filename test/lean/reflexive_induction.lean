import Lean

inductive ReflexiveW : Nat → Prop where
  | mk (x : Nat) (h : ∀ y : Nat, ReflexiveW (Nat.succ y)) : ReflexiveW x

example (x : Nat) : ReflexiveW x → x = x := by
  intro h
  induction h with
  | mk x h ih_h =>
    guard_hyp ih_h : ∀ y : Nat, Nat.succ y = Nat.succ y
    rfl

example (x : Nat) (h : ReflexiveW x) : False := by
  induction h with
  | mk x children ih =>
    guard_hyp ih : ∀ y : Nat, False
    exact ih 0

example (x : Nat) (h : ReflexiveW x) : False := by
  induction h
  case mk x children ih => exact ih 0

inductive DeriveEvidence (base : Nat → Bool) (deps : Nat → List Nat) (leaf : Nat → Bool) : Nat → Prop where
  | mk (x : Nat) (hb : base x = true)
      (hd : ∀ y : Nat, y ∈ deps x → leaf y = false → DeriveEvidence base deps leaf y) :
      DeriveEvidence base deps leaf x

example (base : Nat → Bool) (deps : Nat → List Nat) (leaf : Nat → Bool)
    (x : Nat) (h : DeriveEvidence base deps leaf x) :
    base x = true ∧ ∀ y : Nat, y ∈ deps x → leaf y = false → base y = true := by
  induction h with
  | mk x hb hd ih_hd =>
    guard_hyp ih_hd : ∀ y : Nat, y ∈ deps x → leaf y = false →
      base y = true ∧ ∀ z : Nat, z ∈ deps y → leaf z = false → base z = true
    constructor
    · exact hb
    · intro y hm hl
      exact (ih_hd y hm hl).left

example (x : Nat) (h : ReflexiveW x) : ReflexiveW 1 := by
  cases h with
  | mk x children =>
    fail_if_success assumption
    exact children 0

example (x : Nat) (h : ReflexiveW x) : ReflexiveW 1 := by
  rcases h with ⟨x, children⟩
  fail_if_success assumption
  exact children 0

inductive TwoParents : Prop where
  | mk (left : TwoParents) (value : Nat) (right : TwoParents) : TwoParents

example (h : TwoParents) : False := by
  induction h with
  | mk left value right ih_left ih_right => exact ih_left

-- Meta/Tactic/Induction.lean finalize introduces the minor premise's binders in order: all
-- fields, then the induction hypotheses. `case tag x…` renames the trailing inaccessibles.
example (h : TwoParents) : False := by
  induction h
  case mk ihl ihr => exact ihl

example (h : TwoParents) : False := by
  induction h
  case mk l v r ihl ihr => exact ihr
