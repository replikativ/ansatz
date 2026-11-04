import Lean
open Lean Meta

-- Lean v4.33.1 Meta/Tactic/Rewrite.lean: instantiate eAbst.instantiate1 rhs.
def betaAll (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | h :: t => p h && betaAll p t
def betaG (n : Nat) : Nat := n
theorem betaGEq (n : Nat) : betaG n = n := rfl
theorem betaOne (p : Nat → Bool) (n : Nat) :
    betaAll p [n] = (p n && true) := rfl

example (x : Nat) (h : betaAll (fun r => betaG r == 0) [x] = true) :
    ((x == 0) && true) = true := by
  rw [betaOne] at h
  rw [betaGEq] at h
  exact h

example (x : Nat) (h : ((x == 0) && true) = true) :
    betaAll (fun r => betaG r == 0) [x] = true := by
  rw [betaOne]
  rw [betaGEq]
  exact h

def betaApplyTwo (f : Nat → Nat → Bool) (x y : Nat) : Bool := f x y
theorem betaApplyTwoEq (f : Nat → Nat → Bool) (x y : Nat) :
    betaApplyTwo f x y = f x y := rfl
example (x y : Nat) (h : (x == y) = true) :
    betaApplyTwo (fun r s => betaG r == betaG s) x y = true := by
  rw [betaApplyTwoEq]
  rw [betaGEq]
  exact h

theorem betaOneReverse (p : Nat → Bool) (n : Nat) :
    (p n && true) = betaAll p [n] := rfl
example (x : Nat) (h : betaAll (fun r => betaG r == 0) [x] = true) :
    ((x == 0) && true) = true := by
  rw [← betaOneReverse] at h
  rw [betaGEq] at h
  exact h

-- Check syntax, since definitional equality cannot distinguish beta-redexes.
run_meta do
  let nat := mkConst ``Nat
  let arrow := mkForall `_ .default nat nat
  let ident := mkLambda `x .default nat (.bvar 0)
  let x := mkNatLit 7
  let f ← mkFreshExprMVar arrow
  f.mvarId!.assign ident
  unless (← instantiateMVars (mkApp f x)) == x do throwError "assigned head"
  unless (← instantiateMVars (mkApp f (mkApp f x))) == x do throwError "nested"
  let alias ← mkFreshExprMVar arrow
  alias.mvarId!.assign f
  unless (← instantiateMVars (mkApp alias x)) == x do throwError "chain"
  let k ← mkFreshExprMVar (mkForall `_ .default nat arrow)
  k.mvarId!.assign (mkLambda `x .default nat (mkLambda `y .default nat (.bvar 1)))
  unless (← instantiateMVars (mkApp2 k x (mkNatLit 8))) == x do throwError "two binders"
  unless (← instantiateMVars (mkApp k x)) == mkLambda `y .default nat x do
    throwError "partial application"
  let ret ← mkFreshExprMVar (mkForall `_ .default arrow arrow)
  ret.mvarId!.assign (mkLambda `g .default arrow (.bvar 0))
  unless (← instantiateMVars (mkApp2 ret ident x)) == mkApp ident x do
    throwError "returned lambda must remain applied"
  let z ← mkFreshExprMVar arrow
  z.mvarId!.assign (mkLet `f arrow ident (.bvar 0))
  unless (← instantiateMVars (mkApp z x)) == x do throwError "zeta"
  let md ← mkFreshExprMVar arrow
  md.mvarId!.assign (.mdata {} ident)
  unless (← instantiateMVars (mkApp md x)) == x do throwError "metadata"
  let a ← mkFreshExprMVar nat
  a.mvarId!.assign x
  unless (← instantiateMVars (mkApp ident a)) == mkApp ident x do
    throwError "literal head must remain applied"
