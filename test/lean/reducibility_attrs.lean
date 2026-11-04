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

@[implicit_reducible] def projectionImplicitInstance : Add Nat := instAddNat
@[implicit_reducible] def projectionImplicitWrapper : Nat := @Add.add Nat instAddNat 0 1

open Lean Meta in
run_meta do
  let e := mkAppN (mkConst ``Add.add [Level.zero])
    #[mkConst ``Nat, mkConst ``instAddNat, mkNatLit 0, mkNatLit 1]
  for mode in [TransparencyMode.instances, .implicit] do
    let unfolded ← withTransparency mode (whnf e)
    if unfolded == e then
      throwError "projection failed to unfold"
    unless (← withTransparency .all (isDefEq unfolded (mkNatLit 1))) do
      throwError "projection unfolded to an incorrect value"
  let wrapper := mkConst ``projectionImplicitWrapper
  unless (← withTransparency .instances (whnf wrapper)) == wrapper do
    throwError "implicit wrapper unfolded at instances transparency"
  unless (← withTransparency .implicit (whnf wrapper)) == (← withTransparency .implicit (whnf e)) do
    throwError "implicit wrapper failed to reduce its projection"
  let wrappedInstance := mkAppN (mkConst ``Add.add [Level.zero])
    #[mkConst ``Nat, mkConst ``projectionImplicitInstance, mkNatLit 0, mkNatLit 1]
  for mode in [TransparencyMode.instances, .implicit] do
    unless (← withTransparency mode (whnf wrappedInstance)) == wrappedInstance do
      throwError "projection instance reduction exceeded instances transparency"

section
attribute [local irreducible] Add.add
open Lean Meta in
run_meta do
  let e := mkAppN (mkConst ``Add.add [Level.zero])
    #[mkConst ``Nat, mkConst ``instAddNat, mkNatLit 0, mkNatLit 1]
  for mode in [TransparencyMode.instances, .implicit] do
    unless (← withTransparency mode (whnf e)) == e do
      throwError "irreducible projection unfolded"
  let unfolded ← withTransparency .all (whnf e)
  if unfolded == e then
    throwError "projection failed to unfold at all transparency"
  unless (← withTransparency .all (isDefEq unfolded (mkNatLit 1))) do
    throwError "projection unfolded to an incorrect value"
end

section
set_option allowUnsafeReducibility true
attribute [local reducible] Add.add
open Lean Meta in
run_meta do
  unless (← getReducibilityStatus ``instAddNat) == .instanceReducible do
    throwError "instance status changed"
  let field := mkConst ``Add.add [Level.zero]
  let e := mkAppN field #[mkConst ``Nat, mkConst ``instAddNat, mkNatLit 0, mkNatLit 1]
  let result ← withTransparency .reducible (whnf e)
  if result == e || result.getAppFn.isProj then
    throwError "reducible class field failed to expose its instance field"
  unless (← withTransparency .all (isDefEq result (mkNatLit 1))) do
    throwError "reducible class field returned an incorrect value"
  withLocalDeclD `inst (mkApp (mkConst ``Add [Level.zero]) (mkConst ``Nat)) fun inst => do
    let stuck := mkAppN field #[mkConst ``Nat, inst, mkNatLit 0, mkNatLit 1]
    unless (← withTransparency .reducible (whnf stuck)).getAppFn.isProj do
      throwError "stuck class field did not retain its ordinary unfolding"
end
