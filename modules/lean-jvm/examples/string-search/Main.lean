def anyContains (text : String) (target : Char) : IO Bool :=
  pure (text.any (· == target))

def hasPrefix (needle text : String) : Bool := needle.isPrefixOf text

def anyFailure (text : String) : IO Bool :=
  pure (text.any fun c => (dbgTraceIfShared "predicate leaf" (toString c)).isEmpty)
