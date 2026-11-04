import Lean
def matcherOption (n : Nat) : Option Nat :=
  match n with | 0 => none | k + 1 => some k

def matcherClamp (o : Option Nat) : Nat :=
  match o with
  | none => 0
  | some m => match m.ble 5 with | true => m | false => 5

example (n j : Nat) (e : matcherOption n = some j) : matcherClamp (matcherOption n) ≤ 5 := by
  simp only [matcherClamp, e]
  split
  · rename_i h
    exact Nat.le_of_ble_eq_true h
  · omega

inductive MatcherStore where
  | mk (a b : Nat)

def matcherStoreOption (s : MatcherStore) (o : Option Nat) : Option Nat :=
  match o with
  | none => some 0
  | some m => match s with
    | .mk a b => match m.ble a with | true => some a | false => some b

example (s : MatcherStore) (o : Option Nat) : matcherStoreOption s o ≠ none := by
  intro q
  cases o
  all_goals simp only [matcherStoreOption] at q
  · cases q
  · cases s
    split at q <;> cases q

-- Class projections stay semireducible but unfoldProjInst? reduces concrete
-- instances while whnfMatcher selects an alternative (Lean 4.33.1).
def matcherArithmetic (n : Nat) : Bool :=
  match n + 1 with | 0 => false | _ + 1 => true
example : matcherArithmetic 0 = true := by simp only [matcherArithmetic]

section
attribute [local irreducible] OfNat.ofNat NatCast.natCast Zero.zero One.one
open Lean Meta in
run_meta do
  for field in [``OfNat.ofNat, ``NatCast.natCast, ``Zero.zero, ``One.one] do
    let info ← getConstInfo field
    if (← canUnfoldDefault { transparency := .instances } info) then
      throwError "ordinary permission ignored irreducibility"
    unless (← canUnfoldAtMatcher { transparency := .instances } info) do
      throwError "numeric matcher exception was lost"
  let nat := mkConst ``Nat
  let one := mkNatLit 1
  let terms := #[
    (mkAppN (mkConst ``OfNat.ofNat [Level.zero]) #[nat, one, mkApp (mkConst ``instOfNatNat) one], one),
    (mkAppN (mkConst ``NatCast.natCast [Level.zero]) #[nat, mkConst ``instNatCastNat, one], one),
    (mkAppN (mkConst ``Zero.zero [Level.zero]) #[nat, mkAppN (mkConst ``Zero.mk [Level.zero]) #[nat, mkNatLit 0]], mkNatLit 0),
    (mkAppN (mkConst ``One.one [Level.zero]) #[nat, mkAppN (mkConst ``One.mk [Level.zero]) #[nat, one]], one)]
  for (term, expected) in terms do
    let result ← withTransparency .instances <| withCanUnfoldPred canUnfoldAtMatcher <| whnf term
    if result == term || result.getAppFn.isProj then
      throwError "numeric matcher field stayed folded"
    unless (← withTransparency .all (isDefEq result expected)) do
      throwError "numeric matcher field returned an incorrect value"
end
