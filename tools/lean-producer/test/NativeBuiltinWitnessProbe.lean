import NativeNominalEntryEvidence
import NativeNominalFixtures
import NativeBuiltinWitnessFixtures
import Lean.Elab.BuiltinEvalCommand

/- Compiler-only witnesses in the already-imported fixture Environment.
No raw/boxed callable lookup, fresh importModules, or public admission. -/
open Lean

private def roots : Array Expr :=
  #[mkConst ``NativeBuiltinWitnessFixtures.Containers, mkConst ``NativeNominalFixtures.AST, mkConst ``NativeNominalFixtures.Mixed, mkConst ``NativeNominalFixtures.Scalars, mkConst ``NativeNominalFixtures.Empty,
    mkConst ``NativeNominalFixtures.Singleton, mkConst ``Ordering,
    mkApp (mkConst ``NativeNominalFixtures.Box [.max .zero .zero]) (mkConst ``UInt32),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``Unit),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``Float),
    mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkApp (mkConst ``NativeNominalFixtures.Box [.zero]) (mkConst ``UInt32))]


run_meta do
  let inventory ← NativeNominalEntryEvidence.inventoryTypes roots
  let some mode ← IO.getEnv "NOMINAL_WITNESS_MODE" | throwError "witness mode required"
  if mode == "inventory" then
    logInfo m!"NOMINAL_WITNESS_INVENTORY_JSON {inventory.compress}"
  else if mode == "observe" then
    let some path ← IO.getEnv "NOMINAL_WITNESS_PRODUCTS" | throwError "actual captured products required"
    let manifest ← NativeEntryTransport.checkedIO <| Json.parse (← NativeEntryTransport.readBounded path 4194304)
    unless (← NativeEntryTransport.checkedIO (manifest.getObjValAs? String "schema")) ==
        "lean-jvm-used-module-products/1" do throwError "unexpected private probe manifest schema"
    let rows ← NativeEntryTransport.checkedIO (manifest.getObjValAs? (Array Json) "modules")
    unless rows.size ≤ 256 do throwError "manifest module budget"
    let mut products : NameMap String := {}
    for row in rows do
      let name ← NativeEntryTransport.checkedIO <| NativeEntryTransport.checkedName
        (← NativeEntryTransport.checkedIO (row.getObjVal? "module"))
      let digest ← NativeEntryTransport.checkedIO (row.getObjValAs? String "productSha256")
      unless digest.length == 64 && (products.find? name).isNone do throwError "invalid captured module"
      products := products.insert name digest
    let observation ← NativeNominalEntryEvidence.observeTypeWitnesses roots (fun name => products.find? name)
    let witnesses ← NativeEntryTransport.checkedIO (observation.getObjVal? "runtimeWitnesses")
    let builtins ← NativeEntryTransport.checkedIO (witnesses.getObjValAs? (Array Json) "closedBuiltins")
    let kinds ← builtins.mapM fun row => NativeEntryTransport.checkedIO do
      (← row.getObjVal? "type").getObjValAs? String "kind"
    for kind in #["list", "option", "product", "sum", "except"] do
      unless kinds.contains kind do throwError "missing actual closed builtin witness {kind}"
    unless (← NativeEntryTransport.checkedIO (witnesses.getObjValAs? (Array Json) "ioFamilies")).isEmpty do
      throwError "compiler-only observation must not claim entry IO binding"
    logInfo m!"NOMINAL_WITNESS_OBSERVATIONS_JSON {observation.compress}"
    logInfo "NOMINAL_WITNESS_PROBE_PASS"
  else throwError "unknown witness mode"
