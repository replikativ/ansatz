namespace NativeEntryInitCases
def ordinary : IO Unit := pure ()
def regularAction : IO Unit := pure ()
attribute [init] regularAction
def builtinAction : IO Unit := pure ()
attribute [builtin_init] builtinAction
initialize (pure () : IO Unit)
builtin_initialize (pure () : IO Unit)
end NativeEntryInitCases
