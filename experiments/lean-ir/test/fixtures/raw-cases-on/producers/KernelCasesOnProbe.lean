import Lean.Environment

namespace KernelCasesOnProbe
open Lean

/-- Constructor-only fixture map. Inputs must explicitly omit expected casesOn
answers. This helper supplies no checking/admission/certification authority. -/
@[noinline] def constantMap (constants : @& Array ConstantInfo) : ConstMap :=
  constants.foldl (fun map info => map.insert info.name info) SMap.empty

/-- Compare actual raw type/value with native ConstantInfo oracle. This never
uses the Java checking projection or alpha-only Expr.eqv. All inputs borrowed. -/
@[noinline] def sameDefinition (declaration : @& Declaration) (expected : @& ConstantInfo) : Bool :=
  match declaration, expected with
  | .defnDecl actual, .defnInfo expected =>
    actual.name == expected.name && actual.levelParams == expected.levelParams &&
    actual.type.equal expected.type && actual.value.equal expected.value &&
    actual.hints == expected.hints && actual.safety == expected.safety && actual.all == expected.all
  | _, _ => false

end KernelCasesOnProbe
