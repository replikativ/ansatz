import Init

def metadataFields (path : String) :
    IO ((Int × UInt32) × ((Int × UInt32) × (UInt64 × (UInt64 × Bool)))) := do
  let m ← (System.FilePath.mk path).metadata
  pure ((m.accessed.sec, m.accessed.nsec),
        ((m.modified.sec, m.modified.nsec), (m.byteSize, (m.numLinks, m.type == .file))))

def cursorAndEmpty (path : String) : IO (String × ByteArray × Bool) := do
  let h ← IO.FS.Handle.mk (System.FilePath.mk path) .read
  h.write ByteArray.empty
  h.putStr ""
  let line ← h.getLine
  h.flush
  let rest ← h.read 4096
  let tty ← h.isTty
  pure (line, rest, tty)

def writeErrors (path : String) : IO ((UInt32 × Bool) × (UInt32 × Bool)) := do
  let h ← IO.FS.Handle.mk (System.FilePath.mk path) .read
  let write ← try
    h.write (ByteArray.empty.push 65)
    pure (0, false)
  catch e => pure <| match e with
    | .invalidArgument filename code _ => (code, filename.isNone)
    | _ => (0, false)
  let put ← try
    h.putStr "x"
    pure (0, false)
  catch e => pure <| match e with
    | .invalidArgument filename code _ => (code, filename.isNone)
    | _ => (0, false)
  pure (write, put)

def missingFacts (path : String) : IO (UInt32 × UInt32) := do
  let metadata ← try
    let _ ← (System.FilePath.mk path).metadata
    pure 0
  catch e => pure <| match e with
    | .noFileOrDirectory _ code _ => code
    | _ => 0
  let opened ← try
    let _ ← IO.FS.Handle.mk (System.FilePath.mk path) .read
    pure 0
  catch e => pure <| match e with
    | .noFileOrDirectory _ code _ => code
    | _ => 0
  pure (metadata, opened)

def nulFacts : IO ((UInt32 × Bool) × (UInt32 × Bool)) := do
  let path := "bad" ++ String.singleton (Char.ofNat 0) ++ "path"
  let decode := fun (e : IO.Error) => match e with
    | IO.Error.invalidArgument (some filename) code details =>
      (code, filename == path && details == "string contains NUL bytes")
    | _ => (0, false)
  let metadata ← try
    let _ ← (System.FilePath.mk path).metadata
    pure (0, false)
  catch e => pure (decode e)
  let opened ← try
    let _ ← IO.FS.Handle.mk (System.FilePath.mk path) .read
    pure (0, false)
  catch e => pure (decode e)
  pure (metadata, opened)
