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

-- Type formers and proofs have erased runtime artifacts (ToLCNF.visit).
def recursivePredicate (n : Nat) : Prop :=
  match n with
  | 0 => True
  | k + 1 => recursivePredicate k

theorem recursiveProof (n : Nat) : (0 : Nat) = 0 :=
  match n with
  | 0 => rfl
  | k + 1 => recursiveProof k

example : recursivePredicate 3 := by change True; trivial

-- Retaining acc also requires retaining offset, used in its next recursive value.
def chain {offset acc : Nat} (n : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => @chain offset offset k

example : @chain 2 3 0 = 3 := by native_decide
example : @chain 2 3 1 = 2 := by native_decide
example : @chain 2 3 10000 = 2 := by native_decide

example : (let r := @Nat.rec; @r (fun _ => Nat) 0 (fun _ ih => ih + 1) 5) = 5 := by native_decide
example : (let r := @Nat.rec (fun _ => Nat); r 0 (fun _ ih => ih + 1) 5) = 5 := by native_decide


def wfPredicate (n : Nat) : Prop :=
  if n ≤ 0 then True else wfPredicate (n - 1)
termination_by n
decreasing_by omega

theorem wfProof (n : Nat) : (0 : Nat) = 0 :=
  if h : n ≤ 0 then rfl else wfProof (n - 1)
termination_by n
decreasing_by omega

-- Lean compiles these through rec_eq_recCompiled. Native elimination without a
-- compatible lazy minor ABI must reject the named/runtime minor boundary.
def ignoreIH (_k _ih : Nat) : Nat := 7

def runtimeMinor (minor : Nat → Nat → Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 minor 10000

example : (@Nat.rec (fun _ => Nat) 0 ignoreIH 10000) = 7 := by native_decide
example : runtimeMinor ignoreIH = 7 := by native_decide
example : (@Nat.rec (fun _ => Nat) 0 (fun k => ignoreIH k) 10000) = 7 := by native_decide
