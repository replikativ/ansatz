import Main
def main : IO Unit := do
  unless extByte 255 == 0 do throw (IO.userError "UInt8 wrap")
  unless extSigned 1 == -1 do throw (IO.userError "Int64 negation")
  unless extDouble 1.25 == 1.75 do throw (IO.userError "Float addition")
  unless extSingle 16777216 == 16777216 do throw (IO.userError "Float32 rounding")
  unless extChar '😀' == '😀' do throw (IO.userError "Unicode Char")
  unless extWord 41 == 42 do throw (IO.userError "USize addition")
  unless extArrayPush #[1, 2] 3 == #[1, 2, 3] do throw (IO.userError "Array push")
  unless (extBytesPush ⟨#[0, 255]⟩ 42).data == #[0, 255, 42] do throw (IO.userError "ByteArray push")
  match extSum (.inl true) with
  | .inr true => pure ()
  | _ => throw (IO.userError "Sum branch")
  match extExcept (.error "error") with
  | .error "error" => pure ()
  | _ => throw (IO.userError "Except error")
  unless extConstantByte == 255 && extConstantFloat == 1.5 do throw (IO.userError "Nullary scalar")
  IO.println "PASS native scalar/array/bytes/choice oracle"
