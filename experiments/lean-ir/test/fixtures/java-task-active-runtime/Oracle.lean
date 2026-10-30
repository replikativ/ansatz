import Lean

def record (log : IO.Ref (List String)) (s : String) : BaseIO Unit :=
  log.modify (s :: ·)

def pendingPromise : BaseIO (Task (Option Nat)) := do
  let p ← IO.Promise.new
  return p.result?

structure TokenPair where
  first : IO.CancelToken
  second : IO.CancelToken

def releaseSiblings (log : IO.Ref (List String)) : BaseIO Unit := do
  let first ← IO.CancelToken.new
  first.onSet (record log "drop-first")
  let second ← IO.CancelToken.new
  second.onSet (record log "drop-second")
  let holder ← IO.mkRef (some ({ first, second } : TokenPair))
  holder.set none

def replacementObservation (log : IO.Ref (List String)) : BaseIO Unit := do
  let holder ← IO.mkRef (none : Option IO.CancelToken)
  let tk ← IO.CancelToken.new
  tk.onSet do record log s!"replacement-visible={(← holder.get).isNone}"
  holder.set (some tk)
  holder.set none

def main : IO Unit := do
  let log ← IO.mkRef ([] : List String)
  let p : IO.Promise Nat ← IO.Promise.new
  let source := p.result?
  IO.println s!"initial-ready={← IO.hasFinished source}"
  BaseIO.chainTask source (sync := true) fun _ => record log "first"
  BaseIO.chainTask source (sync := true) fun _ => record log "second"
  BaseIO.chainTask source (sync := true) fun _ => record log "third"
  p.resolve 7
  IO.println s!"callback-order={(← log.get).reverse}"
  IO.println s!"first-result={← IO.wait source}"
  p.resolve 99
  IO.println s!"after-duplicate={← IO.wait p.result?}"
  let dropped ← pendingPromise
  IO.println s!"after-drop={← IO.wait dropped}"
  let tk ← IO.CancelToken.new
  tk.onSet do record log s!"on-set-observed={← tk.isSet}"
  tk.set
  tk.set
  IO.println s!"after-set={← tk.isSet}"
  IO.println s!"final-log={(← log.get).reverse}"
  let drops ← IO.mkRef ([] : List String)
  releaseSiblings drops
  IO.println s!"sibling-drop-order={(← drops.get).reverse}"
  let mutations ← IO.mkRef ([] : List String)
  replacementObservation mutations
  IO.println s!"captured-ref-order={(← mutations.get).reverse}"
