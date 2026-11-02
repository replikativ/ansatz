unsafe def badImpl : IO (Array String) := pure (unsafeCast "leaf")
@[implemented_by badImpl] def nominal : IO (Array String) := pure #[]
@[noinline] def checked : IO (Array String) := nominal

def traceChecked : IO Unit := do
  let xs ← checked
  IO.println "before unsupported trace"
  let out := dbgTraceIfShared "bad" xs
  IO.println out.size
