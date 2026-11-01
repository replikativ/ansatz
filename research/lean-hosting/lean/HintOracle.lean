import Lean

def answer : Nat := 42
def answer2 := answer
abbrev aliasAnswer := answer
def answerViaAlias := aliasAnswer
def idAnswer (x : Nat) : Nat := x
def propAnswer : Prop := True

def hintLabel : Lean.ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular height => s!"regular {height.toNat}"

run_elab
  for name in [``answer, ``answer2, ``aliasAnswer, ``answerViaAlias, ``idAnswer, ``propAnswer] do
    let info ← Lean.getConstInfo name
    match info with
    | .defnInfo value => Lean.logInfo m!"{name}: {hintLabel value.hints}"
    | _ => throwError "expected a definition"

run_elab
  for (name, height) in [(`manualZero, (0 : UInt32)), (`manualMax, (4294967295 : UInt32))] do
    Lean.addDecl <| .defnDecl {
      name, levelParams := [], type := Lean.mkConst ``Nat,
      value := Lean.mkNatLit 42, hints := .regular height, safety := .safe }
    let .defnInfo value ← Lean.getConstInfo name | throwError "missing admitted definition"
    Lean.logInfo m!"kernel admitted {name}: {hintLabel value.hints}"

-- The manually admitted declarations intentionally have no compiled bodies.
noncomputable def afterManualMax := manualMax

run_elab
  let .defnInfo value ← Lean.getConstInfo ``afterManualMax | throwError "missing definition"
  Lean.logInfo m!"afterManualMax: {hintLabel value.hints}"

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Lean, importAll := true, isMeta := true }] {}
    (loadExts := true) (level := .private)
  let mut regular : Nat := 0
  let mut zeroCount : Nat := 0
  let mut large : Nat := 0
  let mut examples : Array String := #[]
  for (name, info) in env.constants.toList do
    if let .defnInfo value := info then
      if let .regular height := value.hints then
        regular := regular + 1
        if height == 0 then
          zeroCount := zeroCount + 1
          if examples.size < 12 then examples := examples.push name.toString
        if height.toNat > 2147483647 then large := large + 1
  IO.println s!"Lean {Lean.versionString} {Lean.githash}"
  IO.println s!"regular={regular} regularZero={zeroCount} regularAboveIntMax={large}"
  IO.println s!"regularZeroExamples={repr examples}"
