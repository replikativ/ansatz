import Lean
open Lean
private partial def levelJson (u : Level) : Json :=
  let (tag, fields) : Nat × Array Json := match u with
    | .zero => (0, #[])
    | .succ a => (1, #[levelJson a])
    | .max a b => (2, #[levelJson a, levelJson b])
    | .imax a b => (3, #[levelJson a, levelJson b])
    | .param _ => (4, #[toJson 0])
    | .mvar _ => (5, #[toJson 0])
  Json.mkObj [("tag", toJson tag), ("fields", toJson fields), ("data", toJson (toString u.data.toNat))]
private def emit (tag : Nat) (before after : Array Level) : IO Unit := do
  let old := if tag == 3 then mkSort before[0]! else mkConst .anonymous before.toList
  let new := if tag == 3 then mkSort after[0]! else mkConst .anonymous after.toList
  IO.println <| (Json.mkObj [("tag", toJson tag), ("before", toJson (before.map levelJson)),
    ("after", toJson (after.map levelJson)), ("beforeData", toJson (toString old.data.toNat)),
    ("afterData", toJson (toString new.data.toNat))]).compress
unsafe def main : IO Unit := do
  let z := Level.zero; let s := Level.succ z; let m := Level.mvar ⟨.anonymous⟩; let p := Level.param .anonymous
  emit 3 #[z] #[s]
  emit 3 #[s] #[m]
  emit 3 #[m] #[p]
  emit 4 #[] #[s]
  emit 4 #[s] #[m,p]
  emit 4 #[m,p] #[]
