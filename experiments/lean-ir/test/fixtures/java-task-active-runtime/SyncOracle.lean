import Lean

/- Deterministic pending synchronous-task reference. All registration that must
   happen before resolution is effectful or forced through an IO.Ref holder.
   No unsafe pointer/exclusivity observation, sleep or asynchronous task is used. -/
namespace SyncTaskOracle

def record (log : IO.Ref (List String)) (event : String) : BaseIO Unit :=
  log.modify (event :: ·)

def nestedPropagation : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let outer : IO.Promise Unit ← IO.Promise.new
  let inner : IO.Promise Unit ← IO.Promise.new
  BaseIO.chainTask inner.result? (sync := true) fun _ => record log "inner-first"
  BaseIO.chainTask inner.result? (sync := true) fun _ => record log "inner-second"
  BaseIO.chainTask outer.result? (sync := true) fun _ => record log "outer-first"
  BaseIO.chainTask outer.result? (sync := true) fun _ => do
    record log "outer-second-enter"
    inner.resolve ()
    record log "outer-second-exit"
  outer.resolve ()
  record log "after-resolve"
  IO.println s!"nested={(← log.get).reverse}"

def losingResolve : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let promise : IO.Promise IO.CancelToken ← IO.Promise.new
  let winner ← IO.CancelToken.new
  winner.set
  promise.resolve winner
  let loser ← IO.CancelToken.new
  loser.onSet (record log "losing-token-drop")
  record log "before-duplicate"
  promise.resolve loser
  record log "after-duplicate"
  let some result ← IO.wait promise.result? | throw <| IO.userError "winner disappeared"
  IO.println s!"duplicate={(← log.get).reverse}"
  IO.println s!"duplicate-winner={← result.isSet}"

def discardedKeepalive : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let promise : IO.Promise Unit ← IO.Promise.new
  -- chainTask discards the returned mapTask; native BaseIO keepalive owns it.
  BaseIO.chainTask promise.result? (sync := true) fun _ => record log "kept-callback"
  record log "before-resolve"
  promise.resolve ()
  record log "after-resolve"
  IO.println s!"keepalive={(← log.get).reverse}"

abbrev Held := IO.Ref (Option (Task (IO.CancelToken × Option Nat)))

/-- The map callback is pure and captures its token as a returned tuple field.
The effectful setter forces the pending map to exist before this action returns.
The token has no remaining owner outside the waiting task's callback capture. -/
def holdPure (source : Task (Option Nat)) (holder : Held)
    (log : IO.Ref (List String)) (dropEvent : String) : BaseIO Unit := do
  let token ← IO.CancelToken.new
  token.onSet (record log dropEvent)
  holder.set (some (source.map (fun value => (token, value)) (sync := true)))

def heldPending (holder : Held) : IO Bool := do
  let some task ← holder.get | throw <| IO.userError "missing held task"
  return !(← IO.hasFinished task)

def dropWaitingPure : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let promise : IO.Promise Nat ← IO.Promise.new
  let holder : Held ← IO.mkRef none
  holdPure promise.result? holder log "pure-token-drop"
  IO.println s!"pure-drop-pending={← heldPending holder}"
  record log "before-drop"
  holder.set none
  record log "after-drop"
  promise.resolve 7
  record log "after-resolve"
  IO.println s!"pure-drop={(← log.get).reverse}"

def dropLaterDetached : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let promise : IO.Promise Nat ← IO.Promise.new
  let holder : Held ← IO.mkRef none
  -- First registration: pure waiting task, retained only by holder.
  holdPure promise.result? holder log "later-token-drop"
  IO.println s!"detached-pending={← heldPending holder}"
  -- Last registration runs first and drops the later entry while source finish
  -- is propagating. This is safe native deactivation, not an unsafe UAF probe.
  BaseIO.chainTask promise.result? (sync := true) fun _ => do
    record log "killer-before"
    holder.set none
    record log "killer-after"
  record log "before-resolve"
  promise.resolve 7
  record log "after-resolve"
  IO.println s!"detached={(← log.get).reverse}"

def cancellationScope : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let promise : IO.Promise Unit ← IO.Promise.new
  let source := promise.result?
  BaseIO.chainTask source (sync := true) fun _ => do
    record log s!"pending-canceled={← IO.checkCanceled}"
    -- The ready/sync fast path introduces no new task scope.
    BaseIO.chainTask (Task.pure ()) (sync := true) fun _ => do
      record log s!"ready-inline-canceled={← IO.checkCanceled}"
    record log s!"pending-after={← IO.checkCanceled}"
  IO.cancel source
  IO.println s!"cancel-pending={!(← IO.hasFinished source)}"
  promise.resolve ()
  record log s!"root-after={← IO.checkCanceled}"
  BaseIO.chainTask (Task.pure ()) (sync := true) fun _ => do
    record log s!"root-inline={← IO.checkCanceled}"
  IO.println s!"cancel-scope={(← log.get).reverse}"

end SyncTaskOracle

def main : IO Unit := do
  SyncTaskOracle.nestedPropagation
  SyncTaskOracle.losingResolve
  SyncTaskOracle.discardedKeepalive
  SyncTaskOracle.dropWaitingPure
  SyncTaskOracle.dropLaterDetached
  SyncTaskOracle.cancellationScope
