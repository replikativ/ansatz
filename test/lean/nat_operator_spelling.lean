import Lean
open Lean Elab Command

-- Extra.elabBinOp preserves the heterogeneous operator and its synthesized instance.
set_option pp.all true in
#check fun (a b : Nat) => a + b
set_option pp.all true in
#check fun (a b : Nat) => a - b
set_option pp.all true in
#check fun (a b : Nat) => a * b

-- Check syntax, rather than only definitional equality with the kernel operations.
run_cmd do
  for (stx, method, inst) in [
      (← `(fun (a b : Nat) => a + b), ``HAdd.hAdd, ``instAddNat),
      (← `(fun (a b : Nat) => a - b), ``HSub.hSub, ``instSubNat),
      (← `(fun (a b : Nat) => a * b), ``HMul.hMul, ``instMulNat)] do
    let e ← liftTermElabM do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let body := e.getLambdaBody
    unless body.isAppOfArity method 6 do
      throwError "unexpected arithmetic head: {body}"
    unless body.getArg! 3 |>.getAppArgs |>.any (·.isConstOf inst) do
      throwError "unexpected arithmetic instance: {body}"

example (f : Nat → Nat) (x y : Nat) (h : f (x + y) = 7) : f (Nat.add x y) = 7 := by
  simp only [Nat.add_eq]
  exact h
example (f : Nat → Nat) (x y : Nat) (h : f (x - y) = 7) : f (Nat.sub x y) = 7 := by
  simp only [Nat.sub_eq]
  exact h
example (f : Nat → Nat) (x y : Nat) (h : f (x * y) = 7) : f (Nat.mul x y) = 7 := by
  simp only [Nat.mul_eq]
  exact h
example (n : Nat) : n ≤ Nat.add n 1 := by apply Nat.le_add_right

inductive SizedList where
  | nil
  | cons (head : Nat) (tail : SizedList)
example (n : Nat) (xs : SizedList) : sizeOf (SizedList.cons n xs) = 1 + n + sizeOf xs := by rfl

example (P : Nat → Prop) (j : Nat) (h : P (Nat.succ j))
    (ih : ∀ k, P k → True) : True := by
  exact ih (j + 1) h

-- A value-position operator is the class method, not binary notation's binop% tree.
def natAddValue : Nat → Nat → Nat := HAdd.hAdd
def natSubValue : Nat → Nat → Nat := HSub.hSub
def natMulValue : Nat → Nat → Nat := HMul.hMul
#guard [2, 3].map (natAddValue 5) == [7, 8]
#guard [2, 3].map (natSubValue 5) == [3, 2]
#guard [2, 3].map (natMulValue 5) == [10, 15]
#guard [5, 2].foldl natAddValue 10 == 17
#guard [5, 2].foldl natSubValue 10 == 3
#guard [5, 2].foldl natMulValue 10 == 100

example (P : Prop) (xs : List Nat) (hd j v : Nat)
    (h : xs[j]? = some v)
    (ih : ∀ (k value : Nat), (hd :: xs)[k]? = some value → P) : P := by
  exact ih (j + 1) v h
