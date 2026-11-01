import Lean.Environment

-- PREPARATION ONLY: uncompiled. Exact emitted borrow/ownership ABI is a gate.
namespace KernelSourceInductivePublication

@[extern "lean_environment_add"]
private opaque insertCheckedConstant
    (env : Lean.Kernel.Environment) (info : Lean.ConstantInfo) : Lean.Kernel.Environment

@[extern "lean_elab_environment_to_kernel_env"]
private opaque checkedKernelEnvironment (env : Lean.Environment) : Lean.Kernel.Environment

@[extern "lean_elab_environment_update_base_after_kernel_add"]
private opaque updateAfterKernelCheck
    (env : Lean.Environment) (kernel : Lean.Kernel.Environment)
    (decl : Lean.Declaration) : Lean.Environment

/-- Atomic publication ONLY of a complete source-generated inductive family.
The host must have strictly generated/validated every member, decoded it using
real Lean constructors and reprojected the exact CI array against that result.
No native kernel call, incomplete-bundle fallback or synthesis happens here. -/
@[noinline] unsafe def postCheckGeneratedFamily
    (env : Lean.Environment) (decl : @& Lean.Declaration)
    (constants : @& Array Lean.ConstantInfo) : Except Lean.Kernel.Exception Lean.Environment := do
  let .inductDecl _ _ types unsafeFlag := decl | throw <| .other "Expected a checked source inductive declaration"
  if unsafeFlag then throw <| .other "Unsafe generated source inductive publication is unsupported"
  if constants.isEmpty || types.isEmpty then throw <| .other "Generated inductive family is empty"
  let all := types.map (·.name)
  let mut expected : Array (Lean.Name × Nat) := #[]
  for type in types do
    expected := expected.push (type.name, 5) |>.push (Lean.Name.str type.name "rec", 7)
    for ctor in type.ctors do expected := expected.push (ctor.name, 6)
  unless expected.size == constants.size do throw <| .other "Generated inductive family is incomplete"
  let mut kernel := checkedKernelEnvironment env
  for info in constants do
    let role ← match info with
      | .inductInfo value => do
        unless value.numNested == 0 && value.all == all && !value.isUnsafe do
          throw <| .other "Unsupported generated inductive metadata"
        pure 5
      | .ctorInfo _ => pure 6
      | .recInfo value => do
        unless value.all == all && !value.isUnsafe do throw <| .other "Generated recursor metadata mismatch"
        pure 7
      | _ => throw <| .other "Unexpected generated inductive family member"
    unless expected.contains (info.name, role) do throw <| .other "Unexpected generated inductive family name/role"
    if kernel.find? info.name |>.isSome then
      throw <| .alreadyDeclared kernel info.name
    kernel := insertCheckedConstant kernel info
  return updateAfterKernelCheck env kernel decl

end KernelSourceInductivePublication
