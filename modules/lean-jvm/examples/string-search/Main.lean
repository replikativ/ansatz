def anyContains (text : String) (target : Char) : IO Bool :=
  pure (text.any (· == target))

def hasPrefix (prefix text : String) : Bool := prefix.isPrefixOf text

def anyFailure (text : String) : IO Bool :=
  pure (text.any fun c => (dbgTraceIfShared "predicate leaf" (toString c)).isEmpty)
