-- Lean 4.33.1 default instances (Meta/Instances.lean defaultInstanceExtension,
-- Elab/SyntheticMVars.lean synthesizeUsingDefault). The #guard_msgs block pins Init's
-- @[default_instance] table, which ansatz.tactic.default-instance/init-default-instances
-- seeds; test/ansatz/tactic/default_instance_test.clj mirrors the examples. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/default_instances.lean
import Lean
open Lean Meta

/--
info: HAdd instHAdd 1000
HAnd instHAndOfAndOp 1000
HAndThen instHAndThenOfAndThen 1000
HAppend instHAppendOfAppend 1000
HDiv instHDiv 1000
HMod instHMod 1000
HMul instHMul 1000
HOr instHOrOfOrOp 1000
HOrElse instHOrElseOfOrElse 1000
HPow instHPow 1000
HSMul instHSMul 1000
HShiftLeft instHShiftLeftOfShiftLeft 1000
HShiftRight instHShiftRightOfShiftRight 1000
HSub instHSub 1000
HXor instHXorOfXorOp 1000
Neg Int.instNegInt 500
OfNat instOfNatNat 100
OfScientific instOfScientificFloat 501
Pow instPowNat 1000
Pow instPowOfHomogeneousPow 1000
String.Slice.Pattern.BackwardPattern String.Slice.Pattern.CharPred.instBackwardPatternForallCharBool 1000
String.Slice.Pattern.ForwardPattern String.Slice.Pattern.CharPred.instForwardPatternForallCharBool 1000
String.Slice.Pattern.ToBackwardSearcher String.Slice.Pattern.CharPred.instToBackwardSearcherForallCharBoolDefaultBackwardSearcher 1000
String.Slice.Pattern.ToForwardSearcher String.Slice.Pattern.CharPred.instToForwardSearcherForallCharBoolDefaultForwardSearcher 1000
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let st := defaultInstanceExtension.getState env
  let mut rows : Array String := #[]
  for (cls, insts) in st.defaultInstances.toList do
    for (inst, prio) in insts do
      if let some idx := env.getModuleIdxFor? inst then
        if env.header.moduleNames[idx.toNat]!.toString.startsWith "Init" then
          rows := rows.push s!"{cls} {inst} {prio}"
  logInfo (String.intercalate "\n" (rows.qsort (· < ·)).toList)

-- `/` on Int: instHDiv (priority 1000) fixes `2 : Int` before OfNat's Nat default (100).
example (a x : Int) (h : x = HDiv.hDiv a 2) : x = HDiv.hDiv a 2 := h
example (a x : Int) (h : 2 * x = a) : x = HDiv.hDiv a 2 := by omega
example : HAdd.hAdd 2 3 = 5 := rfl
example : ∃ n : Int, n = n := by apply (Exists.intro 0); rfl
