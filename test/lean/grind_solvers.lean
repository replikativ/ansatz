-- Init-only pairs for grind preprocessing and the arithmetic solver action.
namespace GrindT15

def groundQuot (n : Nat) : Nat := n / 2
example : groundQuot 0 = 0 := by grind [groundQuot]
example : (17 / 3 : Nat) + 17 % 3 = 7 := by grind
example : (- (9 : Int)) + 4 = -5 := by grind
example : Nat.blt 3 7 = true := by grind [Nat.blt_eq]
example : (3 : Nat) < 7 := by grind
example : ¬ (9 : Nat) < 3 := by grind
example (n : Nat) : (3 : Nat) < 7 ∧ n = n := by grind
example (f : Nat → Nat) (n : Nat) (h : ∀ x, f x = 0) (hn : n < f n) : False := by grind
example (a b : Nat) (h : a < b ∨ b < a) : ¬ a = b := by grind

def bgt (a b : Nat) : Bool := Nat.blt b a
example (a : Nat) : bgt a a = false := by grind [bgt, Nat.blt_eq]
def lexgt (h₁ r₁ s₁ h₂ r₂ s₂ : Nat) : Bool :=
  Nat.blt h₂ h₁ || (Nat.beq h₁ h₂ &&
    (Nat.blt r₂ r₁ || (Nat.beq r₁ r₂ && Nat.blt s₂ s₁)))
example (h r s : Nat) : lexgt h r s h r s = false := by grind [lexgt, Nat.blt_eq, Nat.beq_eq]
example (h r x y : Nat) : lexgt h r x h r y = Nat.blt y x := by grind [lexgt, Nat.blt_eq, Nat.beq_eq]
end GrindT15

namespace GrindT15Review
example : (dite ((3 : Nat) < 7) (fun _ => (1 : Nat)) (fun _ => 2)) = 1 := by grind
example (p : Prop) [Decidable p] (hp : p) (f g : Nat → Nat) (x : Nat) :
    (if p then f else g) x = f x := by grind
example (p : Prop) [Decidable p] (hp : ¬ p) (f g : Nat → Nat → Nat) (x y : Nat) :
    (if p then f else g) x y = g x y := by grind
example (p : Prop) [Decidable p] (hp : p) (f : p → Nat → Nat) (g : ¬ p → Nat → Nat) (x : Nat) :
    (dite p f g) x = f hp x := by grind
example (p : Prop) [Decidable p] (hp : ¬ p)
    (f g : Nat → Nat → Nat) (x y : Nat) :
    (dite p (fun _ => f) (fun _ => g)) x y = g x y := by grind
example (p : Prop) [Decidable p] (f g : Nat → Nat) (x : Nat) :
    (if p then f else g) x = f x ∨ (if p then f else g) x = g x := by grind
end GrindT15Review
