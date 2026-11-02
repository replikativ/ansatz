import Main

-- Emit EDN values independently of JVM codecs. Strings below are fixed fixture
-- errors, so quoted Lean string repr is also EDN; no arbitrary string protocol.
private def nat (n : Nat) : String := toString n
private def encodeBool (b : Bool) : String := if b then "true" else "false"
private def pair (a b : String) : String := "[" ++ a ++ " " ++ b ++ "]"
private def opt (n : Option Nat) : String :=
  match n with | none => "nil" | some n => "{:some " ++ nat n ++ "}"
private def exc (encode : α → String) (x : Except String α) : String :=
  match x with
  | .error e => "{:error " ++ reprStr e ++ "}"
  | .ok a => "{:ok " ++ encode a ++ "}"
private def nums (xs : List Nat) : String :=
  "[" ++ String.intercalate " " (xs.map nat) ++ "]"
private def resultPair (x : Nat × Option Nat) : String := pair (nat x.1) (opt x.2)
private def emit (id value : String) : IO Unit := IO.println (id ++ "\t" ++ value)

def main : IO Unit := do
  let r := readerStateExcept 3 10 false
  emit "reader-ok" (pair (exc nat r.1) (nat r.2))
  let r := readerStateExcept 3 10 true
  emit "reader-error" (pair (exc nat r.1) (nat r.2))
  emit "state-rollback" (exc (fun x => pair (nat x.1) (nat x.2)) (stateRollback 10))
  let r := stRefs 10
  emit "st-refs" (pair (nat r.1) (pair (nat r.2.1) (encodeBool r.2.2)))
  for (id, body, cleanup) in [("ok", false, false), ("body", true, false),
                              ("cleanup", false, true), ("both", true, true)] do
    emit ("est-" ++ id) (exc resultPair (estFinally body cleanup))
    emit ("exceptT-" ++ id) (exc resultPair (exceptTFinally body cleanup))
  emit "baseio" (nums (← baseIORunner 10))
  emit "eio-ok" (exc nat (← eioRunner false))
  emit "eio-error" (exc nat (← eioRunner true))
  emit "state-ref" (exc (fun x => pair (nat x.1) (nat x.2)) (← stateRefRunner 3 10))
  emit "state-ref-discard" (nat (← stateRefDiscard 10))
  emit "io-catch-finally" (nums (← ioCatchFinally 10))
  emit "retained-initial" (nat (← retainedRead))
  emit "retained-plus2" (nat (← retainedBump 2))
  emit "retained-plus3" (nat (← retainedBump 3))
  emit "retained-read" (nat (← retainedRead))
