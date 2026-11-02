import Init

/-- An Ansatz-authored ordinary IO application, not a third-party fixture. -/
def runWriter (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
    let text ← IO.FS.readFile (System.FilePath.mk input)
    IO.FS.writeFile (System.FilePath.mk output) ("processed\n" ++ text)
    let bytes ← IO.FS.readBinFile (System.FilePath.mk input)
    IO.FS.writeBinFile (System.FilePath.mk (output ++ ".bin")) (bytes.push 255)
    let fresh ← IO.FS.Handle.mk (System.FilePath.mk (output ++ ".new")) .writeNew
    fresh.putStr ("é" ++ String.singleton (Char.ofNat 0) ++ "雪")
    fresh.flush
    let existingCode ← try
      let _ ← IO.FS.Handle.mk (System.FilePath.mk (output ++ ".new")) .writeNew
      pure (0 : UInt32)
    catch e => pure <| match e with
      | .alreadyExists _ code _ => code
      | _ => 0
    let update ← IO.FS.Handle.mk (System.FilePath.mk (output ++ ".bin")) .readWrite
    let _ ← update.read 1
    update.rewind
    update.write (ByteArray.empty.push 0 |>.push 255)
    update.flush
    update.truncate
    update.rewind
    let verified ← update.read 4
    let summary ← IO.FS.Handle.mk (System.FilePath.mk (output ++ ".log")) .append
    summary.putStr "written\n"
    summary.rewind
    summary.putStr "done\n"
    summary.flush
    IO.println ("bytes=" ++ toString verified.size ++ "; exists=" ++ toString existingCode.toNat)
    return if existingCode == 17 && verified.size == 2 then 0 else 1
  | _ =>
    IO.eprintln "usage: writer INPUT OUTPUT"
    return 2
