import NativeTypeGraph
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.MutualInductive
import Lean.Elab.Structure

/-!
Native discovery probe, not a published helper or authenticated artifact fixture.
The dummy product lookup below tests explicit provenance custody only; its
digests are not evidence that any compiled product has these bytes.
-/
open Lean

namespace NativeTypeGraphProbe

inductive Op where
  | add
  | multiply

inductive AST where
  | literal (value : Nat)
  | binary (op : Op) (left right : AST)
  | sequence (children : List AST)
  | packed (children : Array AST)

structure Stats where
  label : String
  count : UInt32
  checksum : UInt64
  weight : Float32
  payload : ByteArray
  lastOp : Option Op

universe u
structure Box (α : Type u) where
  value : α

abbrev StatsAlias := Stats

structure Dependent where
  size : Nat
  item : Fin size

structure ProofBearing where
  value : Nat
  valid : value = value

inductive Indexed : Nat → Type where
  | zero : Indexed 0

opaque Hidden : Type := Stats

structure Resource where
  handle : IO.FS.Handle

structure FunctionField where
  callback : Nat → Nat

mutual
  inductive MutualA where
    | next : MutualB → MutualA
  inductive MutualB where
    | stop
    | next : MutualA → MutualB
end

private def rejected (label expected : String) (types : Array Expr)
    (products : NativeTypeGraph.ModuleProducts) : MetaM Unit := do
  let failure : Option String ← try
    discard <| NativeTypeGraph.discover types products
    pure none
  catch e => pure (some (← e.toMessageData.toString))
  let some actual := failure | throwError "unexpected discovery success: {label}"
  unless actual == s!"TypeGraph: {expected}" do
    throwError "unexpected rejection for {label}: {actual}"
  logInfo m!"TYPE_GRAPH_REJECT {label} {actual}"

run_meta do
  let env ← getEnv
  let localModule := env.mainModule
  let sha := String.ofList (List.replicate 64 '0')
  let products : NativeTypeGraph.ModuleProducts := fun n => if n == localModule then some sha else none
  let result ← NativeTypeGraph.discover
    #[mkConst ``AST, mkConst ``Stats,
      mkApp (mkConst ``Box [.max .zero .zero]) (mkConst ``Nat), mkConst ``StatsAlias]
    products
  let .ok roots := result.logical.getObjValAs? (Array Json) "roots"
    | throwError "missing automatic root catalog"
  let .ok definitions := result.logical.getObjValAs? (Array Json) "definitions"
    | throwError "missing automatic definition catalog"
  unless roots.size == 3 && definitions.size == 4 do
    throwError "automatic discovery/alias dedup failed: roots={roots.size}, definitions={definitions.size}"
  let some (.inductInfo astInfo) := env.find? ``AST | throwError "missing native AST declaration"
  unless astInfo.all == [``AST] && astInfo.numNested > 0 do
    throwError "probe must cover compiler-generated nested auxiliaries"
  for (label, reason, type) in #[
      ("dependent", "open/dependent type or universe", mkConst ``Dependent),
      ("proof", "open/dependent type or universe", mkConst ``ProofBearing),
      ("indexed", "unsafe/indexed/reflexive inductive", mkApp (mkConst ``Indexed) (mkNatLit 0)),
      ("opaque", "opaque/noninductive type", mkConst ``Hidden),
      ("resource", "special runtime type has no nominal profile", mkConst ``Resource),
      ("function", "function-valued data", mkConst ``FunctionField),
      ("mutual", "user mutual inductive or nested budget", mkConst ``MutualA)] do
    rejected label reason #[type] products
  rejected "missing-product" "missing defining-module product digest" #[mkConst ``Stats] (fun _ => none)
  rejected "bad-product" "noncanonical product SHA-256" #[mkConst ``Stats] (fun _ => some "bad")
  rejected "open-universe" "open/dependent type or universe"
    #[mkApp (mkConst ``Box [.param `open]) (mkConst ``Nat)] products
  -- Actual emitted data can be consumed by the strict JVM-only model; the
  -- probe never substitutes a handwritten descriptor for native discovery.
  logInfo m!"TYPE_GRAPH_JSON {result.logical.compress}"
  logInfo m!"TYPE_LAYOUTS_JSON {result.layouts.compress}"
  logInfo m!"TYPE_GRAPH_PROBE_PASS roots={roots.size} definitions={definitions.size} nested={astInfo.numNested}"

end NativeTypeGraphProbe
