import Init

/- Only these closed, monomorphic adapters cross the host boundary. -/
def readerStateExcept (env initial : Nat) (fail : Bool) : Except String Nat × Nat :=
  let action : ReaderT Nat (ExceptT String (StateM Nat)) Nat := do
    let delta ← read
    modify (· + delta)
    if fail then throw "body"
    pure (← get)
  (action.run env).run.run initial

-- StateT outside Except rolls back to the handler's input state.
def stateRollback (initial : Nat) : Except String (Nat × Nat) :=
  let action : StateT Nat (Except String) Nat := do
    try
      modify (· + 100)
      throw "body"
    catch _ =>
      modify (· + 1)
      pure (← get)
  action.run initial

def stRefs (initial : Nat) : Nat × (Nat × Bool) := runST fun σ => do
  let ref ← ST.mkRef (σ := σ) initial
  let alias := ref
  let old ← ref.swap (initial + 2)
  alias.modify (· + 3)
  let value ← ref.get
  let same ← ref.ptrEq alias
  pure (old, value, same)

def estFinally (bodyFails cleanupFails : Bool) : Except String (Nat × Option Nat) :=
  runEST fun _ =>
    tryFinally'
      (do
        if bodyFails then throw "body"
        pure 7)
      (fun result => do
        if cleanupFails then throw "cleanup"
        pure result)

def exceptTFinally (bodyFails cleanupFails : Bool) : Except String (Nat × Option Nat) :=
  let action : ExceptT String Id (Nat × Option Nat) :=
    tryFinally'
      (do
        if bodyFails then throw "body"
        pure 7)
      (fun result => do
        if cleanupFails then throw "cleanup"
        pure result)
  action.run

def baseIORunner (initial : Nat) : IO (List Nat) := BaseIO.toIO do
  let ref ← IO.mkRef initial
  let old ← ref.swap (initial + 2)
  ref.modify (· + 3)
  pure [old, ← ref.get]

def eioRunner (fail : Bool) : IO (Except String Nat) :=
  let action : EIO String Nat := do
    if fail then throw "typed"
    pure 23
  EIO.toIO' action

-- ReaderT and ref-backed state run over typed EIO; state survives catch.
def stateRefRunner (env initial : Nat) : IO (Except String (Nat × Nat)) :=
  let action : ReaderT Nat (StateRefT Nat (EIO String)) Nat := do
    let delta ← read
    try
      modify (· + delta)
      throw "typed"
    catch _ => modify (· + 10)
    modify (· + 100)
    pure (← get)
  EIO.toIO' ((action.run env).run initial)

def stateRefDiscard (initial : Nat) : IO Nat :=
  let action : StateRefT Nat IO Nat := do
    modify (· + 5)
    pure (← get)
  action.run' initial

-- Real IO.Error catch, finally, and further mutation all execute in Lean.
def ioCatchFinally (initial : Nat) : IO (List Nat) := do
  let ref ← IO.mkRef initial
  let caught ← try
    ref.modify (· + 1)
    throw (IO.userError "guest")
  catch _ =>
    ref.modify (· + 10)
    ref.get
  finally
    ref.modify (· + 100)
  let finalized ← ref.get
  ref.modify (· + 1000)
  pure [caught, finalized, ← ref.get]

-- Named regular initialization is admitted by the current startup profile.
-- Deliberately not builtin_initialize, anonymous initialization, or host refs.
initialize retainedCounter : IO.Ref Nat ← IO.mkRef 40

def retainedRead : IO Nat := retainedCounter.get

def retainedBump (delta : Nat) : IO Nat := do
  retainedCounter.modify (· + delta)
  retainedCounter.get

def uncaughtUserError (message : String) : IO Nat := throw (IO.userError message)

def legacyUserError : IO Unit := throw (IO.userError "legacy guest error")

def otherIOError : IO Unit := throw (IO.Error.otherError 5 "unprojected guest error")
