import KernelControlShim

open Lean

private def resultCode : Except Kernel.Exception Environment → String
  | .ok _ => "ok"
  | .error .interrupted => "interrupted"
  | .error (.alreadyDeclared _ n) => "alreadyDeclared:" ++ n.toString
  | .error (.declHasMVars _ n _) => "declHasMVars:" ++ n.toString
  | .error (.declHasFVars _ n _) => "declHasFVars:" ++ n.toString
  | .error (.other message) => "other:" ++ message
  | .error _ => "unexpected"

private def axiomDecl (name : Name) (type : Expr := mkSort (.succ .zero))
    (params : List Name := []) : Declaration :=
  .axiomDecl {name, levelParams := params, type, isUnsafe := false}

def main : IO Unit := do
  let env ← mkEmptyEnvironment
  let token ← IO.CancelToken.new
  unless !(← KernelControlShim.cancellationIsSet (some token)) &&
      !(← KernelControlShim.cancellationIsSet none) do
    throw <| IO.userError "new cancellation token was set"
  let .ok admitted := env.addDeclCore 200000000 512 (axiomDecl `A) (some token)
    | throw <| IO.userError "unset token rejected valid declaration"
  token.set
  token.set
  unless ← KernelControlShim.cancellationIsSet (some token) do
    throw <| IO.userError "set cancellation token stayed unset"
  let c := {name := `D, levelParams := [], type := mkSort (.succ .zero) : ConstantVal}
  let tests := #[
    ("axiom", env, axiomDecl `A),
    ("definition", env, Declaration.defnDecl {toConstantVal := c, value := mkSort .zero, hints := .opaque, safety := .safe}),
    ("theorem", env, Declaration.thmDecl {c with value := mkSort .zero, all := [`D]}),
    ("opaque", env, Declaration.opaqueDecl {toConstantVal := c, value := mkSort .zero, isUnsafe := false, all := [`D]}),
    ("alreadyDeclared", admitted, axiomDecl `A),
    ("duplicateParams", env, axiomDecl `A (mkSort (.succ .zero)) [`u, `u]),
    ("mvarType", env, axiomDecl `A (mkMVar {name := `m})),
    ("levelMvarType", env, axiomDecl `A (mkSort (.mvar {name := `u}))),
    ("fvarType", env, axiomDecl `A (mkFVar {name := `x})),
    ("looseType", env, axiomDecl `A (mkBVar 0)),
    ("unknownType", env, axiomDecl `A (mkConst `Unknown))]
  for (label, env, decl) in tests do
    let native := env.addDeclCore 200000000 512 decl (some token)
    let some guest := KernelControlShim.cancelledSingleResult env decl
      | throw <| IO.userError "covered cancellation declaration rejected"
    unless resultCode native == resultCode guest do
      throw <| IO.userError s!"{label}: native {resultCode native}; helper {resultCode guest}"
    IO.println (Json.mkObj [("case", toJson label), ("result", toJson (resultCode native))]).compress
  unless (KernelControlShim.cancelledSingleResult env .quotDecl).isNone do
    throw <| IO.userError "unmodeled quotient cancellation claimed support"

