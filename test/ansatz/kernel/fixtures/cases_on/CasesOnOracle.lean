import Lean.Meta.Constructions.CasesOn
import Lean.Data.Json

namespace CasesOnOracle
universe u
inductive Colour where
  | red | green | blue
structure Pair (α : Type u) where
  left : α
  right : α
inductive Box (α : Type u) : Type u where
  | wrap : α → Box α
inductive Sized (α : Type u) : Nat → Type u where
  | nil : Sized α 0
  | cons : α → Sized α n → Sized α (n + 1)
mutual
  inductive Ping where
    | stop : Nat → Ping
    | next : Pong → Ping
  inductive Pong where
    | next : Ping → Pong
end
inductive Rose where
  | node : List Rose → Rose
inductive ChoiceProp : Prop where
  | left | right
unsafe inductive UnsafeBox where
  | wrap : Nat → UnsafeBox

def notInductive : Nat := 0

def wireName : Lean.Name → Lean.Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str parent part => .arr #[.str "str", wireName parent, .str part]
  | .num parent part => .arr #[.str "num", wireName parent, .str (toString part)]

def resultRow (label : String) (result : Except Lean.Kernel.Exception Lean.Declaration) : Lean.Json :=
  match result with
  | .error (.unknownConstant _ name) => .mkObj [("case", .str label), ("error", .str "unknownConstant"), ("name", wireName name)]
  | .error (.other message) => .mkObj [("case", .str label), ("error", .str "other"), ("message", .str message)]
  | .error _ => .mkObj [("case", .str label), ("error", .str "unexpected-kernel-error")]
  | .ok _ => .mkObj [("case", .str label), ("error", .str "unexpected-success")]
end CasesOnOracle

-- Actual native error payloads, not hand-built Kernel.Exception encodings.
def main : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "Pinned Lean producer mismatch"
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{module := `CasesOnOracle}] {}
  IO.println <| (Lean.Json.mkObj [("schema", .str "cases-on-native-errors/1"), ("leanCommit", .str Lean.githash)]).compress
  let root := Lean.Name.str .anonymous "CasesOnOracle"
  IO.println <| (CasesOnOracle.resultRow "missing" <| Lean.mkCasesOnImp env.toKernelEnv (Lean.Name.str root "missing")).compress
  IO.println <| (CasesOnOracle.resultRow "not-inductive" <| Lean.mkCasesOnImp env.toKernelEnv (Lean.Name.str root "notInductive")).compress
