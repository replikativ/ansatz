import NativeNominalEntryEvidence
import NativeNominalFixtures
import Lean.Elab.BuiltinEvalCommand

/-!
Private source-side candidate core test using the actual already-imported
compiled fixture Environment. A second importModules inside frontend #eval
exceeds the 512 MiB cap; fresh CLI import remains a standalone executable gate.
No executable is linked, entry body executed, pin or SDK BuildReceipt issued.
-/

open Lean

run_meta do
  let env ← getEnv
  let some requestPath ← IO.getEnv "NOMINAL_ENTRY_REQUEST" | throwError "entry probe needs request"
  let request ← NativeEntryTransport.checkedIO <| Json.parse
    (← NativeEntryTransport.readBounded requestPath 65536)
  let mode ← IO.getEnv "NOMINAL_ENTRY_MODE"
  if mode == some "inventory" then
    let document ← NativeNominalEntryEvidence.inventorySelected env request
    logInfo m!"NOMINAL_ENTRY_INVENTORY_JSON {document.compress}"
  else if mode == some "entries" then
    let some productPath ← IO.getEnv "NOMINAL_ENTRY_PRODUCTS" | throwError "entry probe needs real products"
    let products ← NativeEntryTransport.checkedIO <| Json.parse
      (← NativeEntryTransport.readBounded productPath 4194304)
    let document ← NativeNominalEntryEvidence.inspectEntries env request products
    let entries ← NativeEntryTransport.checkedIO (document.getObjValAs? (Array Lean.Json) "entries")
    unless entries.size == 10 do throwError "entry count mismatch"
    logInfo m!"NOMINAL_ENTRY_EVIDENCE_JSON {document.compress}"
    logInfo "NOMINAL_ENTRY_PROBE_PASS"
  else throwError "entry probe mode"
