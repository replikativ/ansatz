-- Init-only grind regressions, paired with grind_v2_test.clj.
namespace GrindStage2Review
example (p : Nat → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬p x := by grind
example (p : Nat → Prop) (a : Nat) (h : ¬ ∃ x, p x) : ¬p a := by grind
example (p : Nat → Prop) (h : (∀ x, p x) = False) : ∃ x, ¬p x := by grind
example (p : Nat → Prop) (a : Nat) (h : (∃ x, p x) = False) : ¬p a := by grind

def app : List Nat → List Nat → List Nat
  | [], ys => ys
  | h :: t, ys => h :: app t ys

def choose (xs : List Nat) (b : Bool) : Nat :=
  match xs with
  | [] => 0
  | h :: _ => if b then h else 0

def ident (x : Nat) := x
example (h : Nat) (t ys : List Nat) : app (h::t) ys = h :: app t ys := by grind [app]
example (x : Nat) : ident x = x := by grind [ident]
example (a b : Nat) : (a + b) + 1 = (a + 1) + b := by grind
example (xs : List Nat) (b : Bool) (h : app xs [] = xs) :
    (if b then app xs [] else xs) = xs := by grind
example (a b c : Nat) (h₁ : Nat.beq a b = true) (h₂ : Nat.beq b c = true) : a = c := by
  grind [Nat.beq_eq]
example (a b : Nat) (h : Nat.ble a b = true) : a ≤ b := by grind [Nat.ble_eq]
example (a b : Nat) (h : ¬ a ≤ b) : b ≤ a := by grind
end GrindStage2Review

namespace GrindRound3Review
example (p q : Prop) (h₁ : p → q) (h₂ : ¬p → q) : q := by grind
example (p q r : Prop) (h₁ : p → q) (h₂ : ¬p → r) (hn : ¬q) : r := by grind
example (a : Nat) (h₀ : a = 0) (h₁ : a = 1) : False := by grind
example (s : String) (h₀ : s = "a") (h₁ : s = "b") : False := by grind
end GrindRound3Review

namespace GrindRound3Predicates
inductive Tag : List Nat → Prop where
  | empty : Tag []
  | single (x : Nat) : Tag [x]
attribute [grind] Tag
example (x : Nat) : Tag [x] := by grind
example (l : List Nat) (h : Tag l) (hn : l ≠ []) (hs : ∀ x, l ≠ [x]) : False := by grind
example (f g : Nat → Nat → Nat → Nat) (x y z : Nat) (h : f = g) :
    f x y z = g x y z := by grind
end GrindRound3Predicates

namespace GrindRound3Insertion
inductive Sorted : List Nat → Prop where
  | nil : Sorted []
  | single (a : Nat) : Sorted [a]
  | cons_cons (a b : Nat) (tl : List Nat) (hab : a ≤ b)
      (hsorted : Sorted (b :: tl)) : Sorted (a :: b :: tl)
attribute [grind] Sorted

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | hd :: tl => if x ≤ hd then x :: hd :: tl else hd :: insertSorted x tl
example (x : Nat) (l : List Nat) (h : Sorted l) : Sorted (insertSorted x l) := by
  induction h <;> grind [insertSorted]
end GrindRound3Insertion

example (p q : Prop) (h₁ : p → q) (h₂ : p → ¬q)
    (h₃ : ¬p → q) (h₄ : ¬p → ¬q) : False := by
  grind (splitImp := true)

example (a b : Nat) (_h : a ≤ b) : True := by
  fail_if_success have : False := by grind (splits := 0)
  trivial
