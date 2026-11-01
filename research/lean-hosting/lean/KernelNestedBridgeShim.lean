import Lean
namespace KernelNestedBridgeShim
@[extern "lean_environment_add"]
private opaque insertCheckedConstant (env : Lean.Kernel.Environment) (info : Lean.ConstantInfo) : Lean.Kernel.Environment
@[extern "lean_elab_environment_to_kernel_env"]
private opaque checkedKernelEnvironment (env : Lean.Environment) : Lean.Kernel.Environment
@[extern "lean_elab_environment_update_base_after_kernel_add"]
private opaque updateAfterKernelCheck (env : Lean.Environment) (kernel : Lean.Kernel.Environment) (decl : Lean.Declaration) : Lean.Environment
/-- Post-check trust boundary for the explicitly enabled bounded source profile.
The host has generated and strictly validated the full restored family, encoded
it through Lean constructors, and compared every CI with that checked result.
No native admission or incomplete-family synthesis is performed here. -/
@[noinline] unsafe def postCheckGeneratedFamily
    (env : Lean.Environment) (decl : @& Lean.Declaration) (constants : Array Lean.ConstantInfo) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .inductDecl [] 0 [type] false := decl
    | throw <| .other "Expected one checked safe parameter-free nested source type"
  unless type.type == Lean.mkSort (.succ .zero) do throw <| .other "Nested source header is outside supported profile"
  let recName := Lean.Name.str type.name "rec"
  let mut expected : Array (Lean.Name × Nat) := #[(type.name, 5), (recName, 7), (recName.appendAfter "_1", 7)]
  for ctor in type.ctors do expected := expected.push (ctor.name, 6)
  unless expected.size == constants.size do throw <| .other "Incomplete checked nested family"
  let mut kernel := checkedKernelEnvironment env
  for info in constants do
    let role ← match info with
      | .inductInfo value => do
        unless value.name == type.name && value.all == [type.name] && value.numParams == 0 &&
            value.numIndices == 0 && value.numNested == 1 && value.isRec && !value.isReflexive && !value.isUnsafe do
          throw <| .other "Nested source inductive metadata mismatch"
        pure 5
      | .ctorInfo value => do
        unless value.induct == type.name && value.numParams == 0 && !value.isUnsafe do
          throw <| .other "Nested source constructor metadata mismatch"
        pure 6
      | .recInfo value => do
        unless value.all == [type.name] && value.numParams == 0 && value.numIndices == 0 &&
            value.numMotives == 2 && !value.k && !value.isUnsafe do
          throw <| .other "Nested source recursor metadata mismatch"
        pure 7
      | _ => throw <| .other "Unexpected checked nested family member"
    unless expected.contains (info.name, role) do throw <| .other "Unexpected nested family name/role"
    if kernel.find? info.name |>.isSome then throw <| .alreadyDeclared kernel info.name
    kernel := insertCheckedConstant kernel info
  return updateAfterKernelCheck env kernel decl
end KernelNestedBridgeShim
