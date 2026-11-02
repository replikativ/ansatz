import Main

private def pair (a b : String) : String := "[" ++ a ++ " " ++ b ++ "]"
private def flag (b : Bool) : String := if b then "true" else "false"
private def codeFlag (p : UInt32 × Bool) : String := pair (toString p.1.toNat) (flag p.2)
private def errors (p : (UInt32 × Bool) × (UInt32 × Bool)) : String := pair (codeFlag p.1) (codeFlag p.2)
private def encodeBytes (data : ByteArray) : String :=
  "[" ++ String.intercalate " " (data.data.toList.map (fun n => toString n.toNat)) ++ "]"
private def cursor (p : String × ByteArray × Bool) : String :=
  pair (encodeBytes p.1.toUTF8) (pair (encodeBytes p.2.1) (flag p.2.2))
private def emit (label value : String) : IO Unit := IO.println (label ++ "\t" ++ value)

def main (args : List String) : IO UInt32 := do
  match args with
  | [first, binary, missing] =>
    let m ← metadataFields first
    let time := fun (p : Int × UInt32) => pair (toString p.1) (toString p.2.toNat)
    emit "metadata" (pair (time m.1) (pair (time m.2.1)
      (pair (toString m.2.2.1.toNat) (pair (toString m.2.2.2.1.toNat) (flag m.2.2.2.2)))))
    emit "cursor-first" (cursor (← cursorAndEmpty first))
    emit "cursor-binary" (cursor (← cursorAndEmpty binary))
    emit "write-errors" (errors (← writeErrors first))
    let missing ← missingFacts missing
    emit "missing" (pair (toString missing.1.toNat) (toString missing.2.toNat))
    emit "nul" (errors (← nulFacts))
    return 0
  | _ => return 2
