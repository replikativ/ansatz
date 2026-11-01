import Lean.Elab.Frontend

namespace KernelDefinitionProbe

/-- Exercise strict kernel admission and guest publication without compiling or
executing the new definition. No imported kernel constants are needed. -/
@[noinline] def checkedIdentitySummary : IO Nat := do
  let env ← Lean.mkEmptyEnvironment
  let name := `kernelIdentity
  let sort := Lean.mkSort (.param `u)
  let type := Lean.mkForall `α .default sort
    (Lean.mkForall `x .default (Lean.mkBVar 0) (Lean.mkBVar 1))
  let value := Lean.mkLambda `α .default sort
    (Lean.mkLambda `x .default (Lean.mkBVar 0) (Lean.mkBVar 0))
  let declaration := Lean.Declaration.defnDecl {
    name, levelParams := [`u], type, value,
    hints := .regular 2, safety := .safe, all := [name] }
  let env ← IO.ofExcept <| (env.addDeclCore 1000000 1000 declaration none)
    |>.mapError (fun _ => "strict identity admission failed")
  return if env.contains name then 1 else 0

end KernelDefinitionProbe

def main : IO Unit := do
  IO.println s!"strict-definition-publication\t{← KernelDefinitionProbe.checkedIdentitySummary}"
