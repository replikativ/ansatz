import Lean

def offsetLoop : Nat → Nat → Nat
  | 0, a => a
  | n+1, a => offsetLoop n (a+1)

#check offsetLoop.eq_1
#check offsetLoop.eq_2
example (n a : Nat) : offsetLoop (n+1) a = offsetLoop n (a+1) := by simp only [offsetLoop]
example (n a : Nat) : offsetLoop (Nat.succ n) a = offsetLoop n (a+1) := by simp only [offsetLoop]
example (n a : Nat) : offsetLoop (n+2) a = offsetLoop n ((a+1)+1) := by simp only [offsetLoop]
example (a : Nat) : offsetLoop 3 a = ((a+1)+1)+1 := by simp only [offsetLoop]
example (n a : Nat) : offsetLoop (n+1) a = offsetLoop n (a+1) := by unfold offsetLoop; cases n <;> rfl
example (n a : Nat) : offsetLoop (n+1) a = offsetLoop n (a+1) := by rw [offsetLoop]
example (n a : Nat) : offsetLoop (n+1) a = offsetLoop n (a+1) := by delta offsetLoop; cases n <;> rfl

def offsetList : List Nat → Nat → Nat
  | [], a => a
  | x::xs, a => offsetList xs (a+x)
example (x a : Nat) (xs : List Nat) : offsetList (x::xs) a = offsetList xs (a+x) := by
  simp only [offsetList]

def offsetPair : Nat → Nat → Nat
  | 0, a => a
  | 1, a => a+1
  | n+2, a => offsetPair n (a+2)
#check offsetPair.eq_3
example (n a : Nat) : offsetPair (n+2) a = offsetPair n (a+2) := by simp only [offsetPair]

def offsetCount : Nat → Nat
  | 0 => 0
  | n+1 => Nat.succ (offsetCount n)
example : offsetCount 3 = 3 := by simp only [offsetCount]
example : offsetCount 0 = 0 := by simp only [offsetCount]

def deltaPresent (n : Nat) := n+1
def deltaAbsent (n : Nat) := n+2
example (P : Nat → Prop) (n : Nat) (h : P (n+1)) : P (deltaPresent n) := by
  delta deltaPresent deltaAbsent
  exact h
example (P : Nat → Prop) (n : Nat) (h : P (n+1)) : P (deltaPresent n) := by
  delta deltaAbsent deltaPresent
  exact h

example (P : Nat → Prop) (x a : Nat) (xs : List Nat) (h : P (offsetList xs (a+x))) :
    P (offsetList (x::xs) a) := by
  simp only [offsetList]
  exact h

namespace Priority
axiom g : Nat → Nat
axiom highResult : Nat → Nat
axiom lowResult : Nat → Nat
@[simp 2000] axiom high (x : Nat) : g (Nat.succ x) = highResult x
@[simp 1000] axiom low (x : Nat) : g x = lowResult x
example (n : Nat) : g (n+1) = highResult n := by simp
end Priority

universe u
def polyOffset (α : Type u) : Nat → α → α
  | 0, a => a
  | n+1, a => polyOffset α n a
example (α : Type u) (P : α → Prop) (n : Nat) (a : α)
    (h : P (polyOffset α n a)) : P (polyOffset α (n+1) a) := by
  simp only [polyOffset]
  exact h

example (P : Nat → Prop) (g highResult : Nat → Nat) (n : Nat)
    (h : ∀ x, P x → g (Nat.succ x) = highResult x) (hp : P n) :
    g (n+1) = highResult n := by
  simp only [h, hp]

example (g result : Nat → Nat) (n : Nat) [Inhabited Nat]
    (h : ∀ x, [Inhabited Nat] → g (Nat.succ x) = result x) :
    g (n+1) = result n := by
  simp only [h]

namespace ConditionalPriority
axiom P : Nat → Prop
axiom g : Nat → Nat
axiom highResult : Nat → Nat
axiom lowResult : Nat → Nat
@[simp 2000] axiom high (x : Nat) : P x → g (Nat.succ x) = highResult x
@[simp 1000] axiom low (x : Nat) : g x = lowResult x
example (n : Nat) (hp : P n) : g (n+1) = highResult n := by simp [hp]
example (n : Nat) : g (n+1) = lowResult (n+1) := by simp
end ConditionalPriority
