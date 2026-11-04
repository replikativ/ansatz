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
