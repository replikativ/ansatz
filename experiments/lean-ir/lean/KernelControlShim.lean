import Lean

open Lean

namespace KernelControlShim

/-- Read the actual guest cancellation flag. Borrowed Option/token/reference
owners remain intact. BaseIO returns a raw Bool, not an IO-result wrapper. -/
@[noinline] def cancellationIsSet (token : @& Option IO.CancelToken) : BaseIO Bool := do
  match token with
  | none => return false
  | some token => token.isSet

private def duplicateParam : List Name → Option Name
  | [] => none
  | name :: rest => if rest.contains name then some name else duplicateParam rest

private def cancelledHeader (env : Kernel.Environment) (value : ConstantVal) :
    Except Kernel.Exception Environment := do
  -- environment.cpp check_constant_val performs these checks BEFORE entering
  -- infer_type_core's first cancellation poll. Preserve their precedence.
  if env.find? value.name |>.isSome then throw <| .alreadyDeclared env value.name
  if let some name := duplicateParam value.levelParams then
    throw <| .other s!"failed to add declaration to environment, duplicate universe level parameter: '{name}'"
  if value.type.hasMVar then throw <| .declHasMVars env value.name value.type
  if value.type.hasFVar then throw <| .declHasFVars env value.name value.type
  if value.type.hasLooseBVars then
    throw <| .other "type checker does not support loose bound variables, replace them with free variables before invoking it"
  -- infer_type_core checks cancellation before examining the expression kind.
  throw .interrupted

/-- Result of checking a supported single declaration with an ALREADY SET token.
The caller first obtains that fact through cancellationIsSet in the same
cooperative snapshot. None explicitly means the declaration's pre-poll order is
not covered (mutual, inductive, quotient), never successful admission. Resource
exhaustion/heartbeat and recursion-limit equivalence remain separate concerns. -/
@[noinline] def cancelledSingleResult (env : @& Environment) (decl : @& Declaration) :
    Option (Except Kernel.Exception Environment) :=
  match decl with
  | .axiomDecl value => some (cancelledHeader env.toKernelEnv value.toConstantVal)
  | .defnDecl value => some (cancelledHeader env.toKernelEnv value.toConstantVal)
  | .thmDecl value => some (cancelledHeader env.toKernelEnv value.toConstantVal)
  | .opaqueDecl value => some (cancelledHeader env.toKernelEnv value.toConstantVal)
  | _ => none

end KernelControlShim
