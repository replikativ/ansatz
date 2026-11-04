-- Lean 4.33.1: Structural.structuralRecursion compiles the predefinition
-- via Basic.addAndCompilePartialRec, keeping the kernel encoding for proofs.
def countdown (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => n
  | k + 1 => if n == 0 then 0 else countdown k (n - 1)

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

def nested (fuel n : Nat) : Nat :=
  let x := n
  match fuel with
  | 0 => x
  | k + 1 => match x with
    | 0 => 0
    | j + 1 => nested k j

def listCountdown (xs : List Nat) (n : Nat) : Nat :=
  match xs with
  | [] => n
  | _ :: t => if n == 0 then 0 else listCountdown t (n - 1)

inductive Fuel where
  | zero
  | succ (n : Fuel)

def custom (fuel : Fuel) (n : Nat) : Nat :=
  match fuel with
  | .zero => n
  | .succ k => if n == 0 then 0 else custom k (n - 1)

def wfCountdown (fuel n : Nat) : Nat :=
  if fuel == 0 then n
  else if n == 0 then 0 else wfCountdown (fuel - 1) (n - 1)
termination_by fuel
decreasing_by simp_all; omega

example : countdown 10000 14 = 0 := by native_decide
example : countdown 10000 10000 = 0 := by native_decide
example : factorial 10 = 3628800 := by native_decide
example : nested 10000 10000 = 0 := by native_decide
example : listCountdown (List.replicate 10000 0) 10000 = 0 := by native_decide
example : custom (.succ .zero) 1 = 0 := by native_decide
example : wfCountdown 10000 14 = 0 := by native_decide

def listLoop (n : Nat) : List Nat :=
  let rec collect (fuel : Nat) (xs : List Nat) : List Nat :=
    match fuel with
    | 0 => xs
    | k + 1 => collect k ((k + 1) :: xs)
  collect n []

example : listLoop 5 = [1, 2, 3, 4, 5] := by native_decide

def offsetSum {offset : Nat} (n : Nat) : Nat :=
  match n with
  | 0 => offset
  | k + 1 => offset + @offsetSum offset k

example : @offsetSum 2 3 = 8 := by native_decide
