import Lean.Elab.Frontend

namespace HostedFileProbe

/-- Prepare the exact empty-environment compiler bootstrap for hosted prelude
file experiments. Each marker goes through the normal strict declaration API;
this helper neither compiles user code nor substitutes native evaluation. -/
@[noinline] def preparePrelude : IO (Lean.Environment × Lean.Options) := do
  let mut env ← Lean.mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := Lean.mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "compiler marker admission failed")
  return (env, {})

end HostedFileProbe

def main : IO Unit := do
  let (env, _) ← HostedFileProbe.preparePrelude
  unless [`lcAny, `lcErased, `lcVoid].all env.contains do
    throw <| IO.userError "missing compiler bootstrap marker"
  IO.println "prelude-environment: passed"
