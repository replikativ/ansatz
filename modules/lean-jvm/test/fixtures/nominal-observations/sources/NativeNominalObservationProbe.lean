import NativeNominalEntryEvidence
import NativeNominalFixtures
import Lean.Elab.BuiltinEvalCommand

/-!
Two separate native invocations: inventory first, then observation with actual
captured imported module products. No dummy SHA or partial graph is published.
This probe is private native validation, not a source-build/artifact issuer.
-/
open Lean
open NativeNominalFixtures

private def roots : Array Expr :=
  #[mkConst ``NativeNominalFixtures.AST, mkConst ``NativeNominalFixtures.Mixed, mkConst ``NativeNominalFixtures.Scalars, mkConst ``NativeNominalFixtures.Empty,
    mkConst ``NativeNominalFixtures.Singleton, mkConst ``Ordering,
    mkApp (mkConst ``NativeNominalFixtures.Box [.max .zero .zero]) (mkConst ``UInt32),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``Unit),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``Float),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``UInt32))]

private def readProducts (path : String) : IO (NativeTypeGraph.ModuleProducts × Json) := do
  let text ← NativeEntryTransport.readBounded path 4194304
  let data ← NativeEntryTransport.checkedIO (Json.parse text)
  let schema ← NativeEntryTransport.checkedIO (data.getObjValAs? String "schema")
  unless schema == "lean-jvm-probe-module-products/1" do throw <| IO.userError "unknown probe product schema"
  let rows ← NativeEntryTransport.checkedIO (data.getObjValAs? (Array Json) "modules")
  unless rows.size ≤ 256 do throw <| IO.userError "probe product count"
  let mut products : NameMap String := {}
  for row in rows do
    let module ← NativeEntryTransport.checkedIO (NativeEntryTransport.checkedName
      (← NativeEntryTransport.checkedIO (row.getObjVal? "module")))
    let sha ← NativeEntryTransport.checkedIO (row.getObjValAs? String "productSha256")
    unless (products.find? module).isNone do throw <| IO.userError "duplicate probe product"
    products := products.insert module sha
  return (fun module => products.find? module, data)

run_meta do
  let inventory ← NativeNominalEntryEvidence.inventoryTypes roots
  let .ok modules := inventory.getObjValAs? (Array Json) "requiredModules"
    | throwError "inventory has no required module catalog"
  let .ok count := inventory.getObjValAs? Nat "nominalDefinitions"
    | throwError "inventory has no definition count"
  unless modules.size == 2 && count == 11 && (inventory.getObjVal? "typeGraph").toOption.isNone do
    throwError "inventory must report complete used origins without an admitted graph"
  let mode ← IO.getEnv "NOMINAL_PROBE_MODE"
  if mode == some "inventory" then
    logInfo m!"NOMINAL_ORIGIN_INVENTORY_JSON {inventory.compress}"
  else if mode == some "observe" then
    let some path ← IO.getEnv "NOMINAL_PROBE_PRODUCTS" | throwError "probe needs actual product manifest"
    let (products, manifest) ← readProducts path
    let observations ← NativeNominalEntryEvidence.observeTypes roots products
    let .ok checks := observations.getObjValAs? (Array Json) "rootTypeChecks"
      | throwError "missing native root DefEq observations"
    unless checks.size == 10 do throwError "canonical root alignment failed"
    logInfo m!"NOMINAL_PRODUCTS_JSON {manifest.compress}"
    logInfo m!"NOMINAL_OBSERVATIONS_JSON {observations.compress}"
    for (label, expected, type) in #[
        ("dependent", "TypeGraph: open/dependent type or universe", mkConst ``NativeNominalFixtures.Dependent),
        ("proof", "TypeGraph: proof-valued field/parameter", mkConst ``NativeNominalFixtures.ProofBearing)] do
      for mode in #["inventory", "observe"] do
        let failure : Option String ← try
          if mode == "inventory" then discard <| NativeNominalEntryEvidence.inventoryTypes #[type]
          else discard <| NativeNominalEntryEvidence.observeTypes #[type] products
          pure none
        catch e => pure (some (← e.toMessageData.toString))
        unless failure == some expected do
          throwError "common {mode} classifier refusal differs for {label}: {failure}"
        logInfo m!"NOMINAL_CLASSIFIER_REJECT {mode} {label} {expected}"
    let missing : Option String ← try
      discard <| NativeNominalEntryEvidence.observeTypes roots (fun _ => none)
      pure none
    catch e => pure (some (← e.toMessageData.toString))
    unless missing == some "TypeGraph: missing defining-module product digest" do
      throwError "missing product evidence was not refused: {missing}"
    logInfo "NOMINAL_OBSERVATION_PROBE_PASS"
  else throwError "set NOMINAL_PROBE_MODE to inventory or observe"
