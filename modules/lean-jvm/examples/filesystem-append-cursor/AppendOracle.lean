import Init

def appendCursorOracle : IO Unit := do
  let initial ← IO.FS.Handle.mk "append-initial" .append
  initial.truncate
  let positioned ← IO.FS.Handle.mk "append-rewind" .append
  positioned.rewind
  positioned.truncate
  let flushed ← IO.FS.Handle.mk "append-rewind-flush" .append
  flushed.rewind
  flushed.flush
  flushed.truncate
  let unsynced ← IO.FS.Handle.mk "append-write-truncate" .append
  unsynced.putStr "X"
  unsynced.truncate
  let synced ← IO.FS.Handle.mk "append-write-flush-truncate" .append
  synced.putStr "X"
  synced.flush
  synced.truncate
  let repeated ← IO.FS.Handle.mk "append-rewind-write" .append
  repeated.putStr "X"
  repeated.rewind
  repeated.putStr "Y"
  repeated.flush

def main : IO Unit := appendCursorOracle
