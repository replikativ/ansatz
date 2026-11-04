import Lean

namespace ReducibilityFixture
@[reducible] def regularReducible : Nat := 1
abbrev abbreviation : Nat := 1
@[irreducible] def hidden : Nat := 1
@[implicit_reducible] def implicitOnly : Nat := 1
@[instance_reducible] def instanceOnly : Nat := 1
def ordinary : Nat := 1
def changedInImport : Nat := 1
class Sample where
  value : Nat
instance sample : Sample := ⟨1⟩
end ReducibilityFixture

-- Lean 4.33.1 ReducibilityAttrs.lean:getReducibilityStatus and
-- Meta/GetUnfoldableConst.lean:canUnfoldDefault; regular hints are independent.
open Lean Meta in
run_meta do
  for (n, expected) in [(`outParam, ReducibilityStatus.reducible),
      (`semiOutParam, .reducible), (`ReducibilityFixture.regularReducible, .reducible),
      (`ReducibilityFixture.abbreviation, .reducible), (`ReducibilityFixture.hidden, .irreducible),
      (`ReducibilityFixture.implicitOnly, .implicitReducible),
      (`ReducibilityFixture.instanceOnly, .instanceReducible),
      (`ReducibilityFixture.sample, .instanceReducible), (`ReducibilityFixture.ordinary, .semireducible)] do
    unless (← getReducibilityStatus n) == expected do
      throwError "unexpected reducibility status: {n}"
    let info ← getConstInfo n
    for mode in [TransparencyMode.none, .reducible, .instances, .implicit, .default, .all] do
      let expectedUnfold := match mode with
        | .none => false
        | .all => true
        | .default => expected != .irreducible
        | m => expected == .reducible ||
            (expected == .instanceReducible && (m == .instances || m == .implicit)) ||
            (expected == .implicitReducible && m == .implicit)
      unless (← canUnfoldDefault { transparency := mode } info) == expectedUnfold do
        throwError "unexpected unfolding permission: {n}"

section
attribute [local irreducible] Add.add
open Lean Meta in
run_meta do
  let e := mkAppN (mkConst ``Add.add [Level.zero])
    #[mkConst ``Nat, mkConst ``instAddNat, mkNatLit 0, mkNatLit 1]
  unless (← withTransparency .instances (whnf e)) == e do
    throwError "irreducible projection unfolded at instances transparency"
  let unfolded ← withTransparency .all (whnf e)
  if unfolded == e then
    throwError "projection failed to unfold at all transparency"
  unless (← withTransparency .all (isDefEq unfolded (mkNatLit 1))) do
    throwError "projection unfolded to an incorrect value"
end
