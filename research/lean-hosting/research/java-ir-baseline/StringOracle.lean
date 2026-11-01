def emitString (label : String) (s : String) : IO Unit := do
  let bytes := s.toUTF8.data.toList.map (fun b => toString b.toNat)
  IO.println ("string|" ++ label ++ "|" ++ toString s.utf8ByteSize ++ "|" ++
    String.intercalate "," bytes)

partial def emitPositions (s : String) (pos : s.Pos) : IO Unit := do
  if h : pos = s.endPos then
    pure ()
  else
    let next := pos.next h
    IO.println ("position|" ++ toString pos.offset.byteIdx ++ "|" ++
      toString (pos.get h).toNat ++ "|" ++ toString next.offset.byteIdx)
    emitPositions s next

def main : IO Unit := do
  let s := "Aé€😀\n"
  emitString "empty" ""
  emitString "unicode" s
  emitString "nul" ("A" ++ String.singleton (Char.ofNat 0) ++ "B")
  emitString "push" ("A".push (Char.ofNat 128512))
  emitString "append" (s ++ s)
  emitString "ofList" (String.ofList s.toList)
  emitPositions s s.startPos
