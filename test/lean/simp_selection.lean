import Lean

def selectedInner (b : Bool) : Nat := match b with | false => 13 | true => 21
def selectedOuter (b : Bool) : Nat := selectedInner b

def selectedRec : List Nat → Nat
  | [] => 0
  | _ :: tail => selectedRec tail

-- guard_target checks syntax, unlike a defeq-based change/rfl assertion.
example (b : Bool) (P : Nat → Prop) (h : P (selectedInner b)) : P (selectedOuter b) := by
  simp only [selectedOuter]
  guard_target =ₛ P (selectedInner b)
  exact h
example (P : Nat → Prop) (h : P (selectedInner true)) : P (selectedOuter true) := by
  simp only [selectedOuter]
  guard_target =ₛ P (selectedInner true)
  exact h
example (b : Bool) (P : Nat → Prop) (h : P (selectedInner b)) : P (selectedInner b) := by
  try simp only []
  guard_target =ₛ P (selectedInner b)
  exact h
example (P : Nat → Prop) (h : P 21) : P (selectedInner true) := by
  simp only [selectedInner]
  guard_target =ₛ P 21
  exact h
example (P : Nat → Prop) (h : P 0) : P (selectedRec []) := by
  simp only [selectedRec]
  guard_target =ₛ P 0
  exact h
example (x : Nat) (h : (none : Option Nat) = some x) : False := by simp at h
example (x : Nat) (xs : List Nat) (h : [] = x :: xs) : False := by simp at h
inductive SelectedChoice (A : Type) where | left : A → SelectedChoice A | right : A → SelectedChoice A
example (x : Nat) (h : SelectedChoice.left x = SelectedChoice.right x) : False := by simp at h
example (x : Nat) (h : (none : Option Nat) = some x) : False := by
  fail_if_success simp only [] at h
  simp at h

structure SelectedStore where
  wallet : Nat
  live : Nat
def selectedAmount (x : Nat) : Option Nat := match x with | 0 => none | n+1 => some n
def selectedHeld (c : Bool) (live : Nat) (_i : Nat) : Option Nat :=
  match c with | false => some 0 | true => some live
def selectedSpendH (_s : SelectedStore) (_i n : Nat) (h : Option Nat) : Nat :=
  match h with | none => 0 | some m => n + m
def selectedSpendN (c : Bool) (s : SelectedStore) (i x : Nat) : Nat :=
  match selectedAmount x with
  | none => 0
  | some n => match s with | .mk _ live => selectedSpendH s i n (selectedHeld c live i)
example (c : Bool) (s : SelectedStore) (i x : Nat) (P : Nat → Prop)
    (h : P (match selectedAmount x with | none => 0 | some n => selectedSpendH s i n (selectedHeld c s.live i))) : P (selectedSpendN c s i x) := by
  simp only [selectedSpendN]
  guard_target =ₛ P (match selectedAmount x with | none => 0 | some n => selectedSpendH s i n (selectedHeld c s.live i))
  exact h

def selectedTruthy (x : Nat) : Bool := match x with | 0 => false | _+1 => true
def selectedPick (b : Bool) (x y : Nat) : Nat := match b with | false => y | true => x
def selectedSeq1 (o : Bool) (fr : Nat → Nat) (done : Nat) : Nat :=
  match o with | true => done | false => fr done
example (P : Nat → Prop) (h : P (selectedPick (selectedTruthy 0) 13 21)) :
    P (selectedSeq1 true id (selectedPick (selectedTruthy 0) 13 21)) := by
  simp only [selectedSeq1]
  guard_target =ₛ P (selectedPick (selectedTruthy 0) 13 21)
  exact h
example (P : (Bool → Nat) → Prop) (h : P selectedOuter) : P selectedOuter := by
  try simp only [selectedOuter]
  guard_target =ₛ P selectedOuter
  exact h
example (x : Nat) (h : (none : Option Nat) = some x) : False := by
  simp only [reduceCtorEq] at h
example (P : Nat → Prop) (h : P 13) : P ((fun n : Nat => n) 13) := by
  simp only []
  guard_target =ₛ P 13
  exact h
example (P : Nat → Prop) (h : P 13) : P (let n := 13; n) := by
  simp only []
  guard_target =ₛ P 13
  exact h
example (P : Nat → Prop) (h : P 13) : P ((13, 21).1) := by
  simp only []
  guard_target =ₛ P 13
  exact h

example (P : Prop → Prop) (h : P (0 ≤ 1 : Prop)) : P (0 ≤ 1 : Prop) := by
  try simp only []
  guard_target =ₛ P (0 ≤ 1 : Prop)
  exact h
example (P : Prop → Prop) (h : P True) : P (0 ≤ 1 : Prop) := by
  simp only [Nat.reduceLeDiff]
  guard_target =ₛ P True
  exact h
example (P : Prop → Prop) (h : P False) : P (2 ≤ 1 : Prop) := by
  simp (config := { decide := false })
  guard_target =ₛ P False
  exact h
example (h : (2 : Nat) ≤ 1) : False := by simp at h

example (A G : Type) (f : G → A → G) (p : A → Bool) (l : List A) :
    ∀ b, List.foldl f b (List.filter p l) =
      List.foldl (fun acc x => match p x with | true => f acc x | false => acc) b l := by
  induction l with
  | nil => intro b; simp only [List.filter, List.foldl]
  | cons head tail ih =>
    intro b
    simp only [List.filter, List.foldl]
    cases hp : p head <;> simp only [List.foldl] <;> exact ih _

example (h : ("alpha" : String) = "beta") : False := by simp at h
example (P : Prop → Prop) (h : P False) : P (("alpha" : String) = "beta") := by
  simp only [String.reduceEq]
  guard_target =ₛ P False
  exact h
example (P : Prop → Prop) (h : P True) : P ((2 : Int) ≠ -1) := by
  simp only [Int.reduceNe]
  guard_target =ₛ P True
  exact h
example (P : Prop → Prop) (h : P False) : P ('a' = 'b') := by
  simp only [Char.reduceEq]
  guard_target =ₛ P False
  exact h
example (P : Nat → Prop) (h : P 5) : P ((2 : Nat) + 3) := by
  simp only [Nat.reduceAdd]
  guard_target =ₛ P 5
  exact h
example (P : Int → Prop) (h : P 5) : P ((2 : Int) + 3) := by
  simp only [Int.reduceAdd]
  guard_target =ₛ P 5
  exact h
-- Int `/` and `%` are Euclidean (Int.ediv / Int.emod)
example (P : Int → Prop) (h : P (-2)) : P ((-3 : Int) / 2) := by
  simp only [Int.reduceDiv]
  exact h
example (P : Int → Prop) (h : P 1) : P ((3 : Int) % (-2)) := by
  simp only [Int.reduceMod]
  exact h
example (P : Int → Prop) (h : P 2) : P ((-12 : Int) % (-7)) := by
  simp only [Int.reduceMod]
  exact h
example (P : Int → Prop) (h : P 0) : P ((5 : Int) / 0) := by
  simp only [Int.reduceDiv]
  exact h
example (P : Int → Prop) (h : P (-5)) : P ((-5 : Int) % 0) := by
  simp only [Int.reduceMod]
  exact h
example (P : Nat → Prop) (h : P 2) : P (if _h : True then 2 else 3) := by
  simp only [reduceDIte]
  guard_target =ₛ P 2
  exact h
example (b : Bool) (P : Nat → Prop) :
    P (match b with | false => 13 | true => 21) → P (selectedInner b) := by
  simp only [selectedInner]
  guard_target =ₛ P (match b with | false => 13 | true => 21) →
    P (match b with | false => 13 | true => 21)
  intro h
  exact h
