initialize unsupportedDuringInit : String ← do
  IO.println "before unsupported initializer"
  pure (dbgTraceIfShared "initializer leaf" "untracked")

def main : IO Unit := IO.println unsupportedDuringInit
