import Init

/- A deliberately small pure reference. Identifiers and family provisioning are
   supplied by the trusted caller; this is not a capability implementation. -/
namespace KlaraBranchModel

abbrev CellId := Nat
abbrev Store := CellId → Nat

def write (s : Store) (id : CellId) (value : Nat) : Store :=
  fun other => if other = id then value else s other

def fork (s : Store) : Store × Store := (s, s)

theorem read_write_same (s : Store) (id value : Nat) :
    write s id value id = value := by exact if_pos rfl

theorem read_write_other (s : Store) (id other value : Nat) (h : other ≠ id) :
    write s id value other = s other := by exact if_neg h

theorem alias_observes_write (s : Store) (direct alias value : Nat)
    (h : alias = direct) : write s direct value alias = value := by
  subst alias
  exact read_write_same s direct value

-- Retaining the old store and writing one fork does not mutate either sibling.
theorem fork_isolation (s : Store) (id value other : Nat) :
    (write (fork s).1 id value id = value) ∧
    ((fork s).2 other = s other) := by
  exact ⟨read_write_same s id value, rfl⟩

inductive Phase where
  | open | claimed (branch : Nat) | complete (branch : Nat) | incomplete (branch : Nat)
  deriving BEq, Repr, DecidableEq

structure Family where
  phase : Phase
  attempts : Nat := 0
  receipts : Nat := 0
  deriving Repr

def provision : Family := ⟨.open, 0, 0⟩

-- A family admits one choice. Neither copying a branch store nor retaining an
-- old *guest* snapshot provisions a new family. Family state is external.
def choose (f : Family) (branch : Nat) : Option Family :=
  match f.phase with
  | .open => some { f with phase := .claimed branch }
  | .claimed _ => none
  | .complete _ => none
  | .incomplete _ => none

theorem choice_claims (f g : Family) (branch : Nat)
    (h : choose f branch = some g) : g.phase = .claimed branch := by
  cases f with
  | mk phase attempts receipts =>
    cases phase with
    | «open» =>
      have eq := Option.some.inj h
      subst g
      rfl
    | claimed _ => cases h
    | complete _ => cases h
    | incomplete _ => cases h

theorem at_most_one_choice (f g : Family) (first second : Nat)
    (h : choose f first = some g) : choose g second = none := by
  unfold choose
  rw [choice_claims f g first h]

-- The caller supplies callback outcomes in order. Stop at the first failure;
-- it counts as an attempt, never a receipt. Even [] closes the chosen family.
-- These are synthetic outcomes, not IO or a theorem about the actual callback.
def tally : List Bool → Nat × Nat × Bool
  | [] => (0, 0, true)
  | false :: _ => (1, 0, false)
  | true :: tail =>
    let (attempts, receipts, ok) := tally tail
    (attempts + 1, receipts + 1, ok)

def settle (f : Family) (outcomes : List Bool) : Option Family :=
  match f.phase with
  | .claimed branch =>
    let (attempts, receipts, ok) := tally outcomes
    some ⟨if ok then .complete branch else .incomplete branch, attempts, receipts⟩
  | .open => none
  | .complete _ => none
  | .incomplete _ => none

def terminal : Phase → Prop
  | .complete _ => True
  | .incomplete _ => True
  | .open => False
  | .claimed _ => False

theorem settlement_terminal (f g : Family) (outcomes : List Bool)
    (h : settle f outcomes = some g) : terminal g.phase := by
  cases f with
  | mk phase attempts receipts =>
    cases phase with
    | «open» => cases h
    | complete _ => cases h
    | incomplete _ => cases h
    | claimed branch =>
      unfold settle at h
      cases ht : tally outcomes with
      | mk count rest =>
        cases rest with
        | mk receipts ok =>
          rw [ht] at h
          cases ok <;> (have eq := Option.some.inj h; subst g; trivial)

theorem terminal_no_choice (f : Family) (branch : Nat) (h : terminal f.phase) :
    choose f branch = none := by
  cases f with
  | mk phase attempts receipts =>
    cases phase with
    | «open» => cases h
    | claimed _ => cases h
    | complete _ => rfl
    | incomplete _ => rfl

theorem terminal_no_replay (f : Family) (outcomes : List Bool) (h : terminal f.phase) :
    settle f outcomes = none := by
  cases f with
  | mk phase attempts receipts =>
    cases phase with
    | «open» => cases h
    | claimed _ => cases h
    | complete _ => rfl
    | incomplete _ => rfl

theorem settlement_no_replay (f g : Family) (xs ys : List Bool)
    (h : settle f xs = some g) : settle g ys = none :=
  terminal_no_replay g ys (settlement_terminal f g xs h)

theorem settlement_no_second_adoption (f g : Family) (xs : List Bool) (branch : Nat)
    (h : settle f xs = some g) : choose g branch = none :=
  terminal_no_choice g branch (settlement_terminal f g xs h)

theorem failure_stops (tail : List Bool) : tally (false :: tail) = (1, 0, false) := rfl

theorem receipt_bound (xs : List Bool) : (tally xs).2.1 ≤ (tally xs).1 := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases x
    · exact Nat.zero_le 1
    · exact Nat.add_le_add_right ih 1

-- Concrete theorem: the third outcome is ignored after the second fails.
example : settle ⟨.claimed 10, 0, 0⟩ [true, false, true] =
    some ⟨.incomplete 10, 2, 1⟩ := rfl

def storeObservation (base left right : Nat) : List Nat :=
  let original : Store := fun _ => base
  let children := fork original
  let direct : CellId := 0
  let alias : CellId := direct
  let l := write children.1 direct left
  let r := write children.2 direct right
  [original direct, l direct, l alias, r direct, r alias, l 1, r 1]

def sampleRows : List (Nat × Nat × Nat × List Nat) :=
  [0, 1, 2].flatMap fun base =>
    [0, 10, 20].flatMap fun left =>
      [0, 10, 20].map fun right =>
        (base, left, right, storeObservation base left right)

end KlaraBranchModel

open KlaraBranchModel

def main : IO Unit := do
  for (base, left, right, observations) in sampleRows do
    IO.println ("{" ++ s!"\"kind\":\"store\",\"base\":{base},\"left\":{left},\"right\":{right},\"observations\":{repr observations}" ++ "}")
  let chosen := (choose provision 10).getD provision
  let complete := (settle chosen [true, true]).getD provision
  let incomplete := (settle chosen [true, false, true]).getD provision
  IO.println ("{" ++ s!"\"kind\":\"authority\",\"secondChoiceRejected\":{(choose chosen 20).isNone},\"completeAttempts\":{complete.attempts},\"completeReceipts\":{complete.receipts},\"completeReplayRejected\":{(settle complete [true]).isNone},\"incompleteAttempts\":{incomplete.attempts},\"incompleteReceipts\":{incomplete.receipts},\"incompleteReplayRejected\":{(settle incomplete [true]).isNone},\"incompleteChoiceRejected\":{(choose incomplete 20).isNone}" ++ "}")
