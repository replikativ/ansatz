/-
Copyright (c) 2026 Simmis contributors.
Released under Apache 2.0 license as described in LICENSE.

Bounded semantic oracle for the pinned official Lean runtime. No address/hash
numbers are compared. IO.Ref separates repeated constructor requests; physical
allocation identity is not inferred merely from source let bindings.
-/
import Lean
open Lean
namespace FoldConstsOracle
private def render (ns : Array Name) : String :=
  String.intercalate "," (ns.toList.map Name.toString)
private def freshConst (r : IO.Ref Name) : IO Expr := do
  let n ← r.get
  pure (.const n [])
private unsafe def observed (e : Expr) : Array Name :=
  Expr.FoldConstsImpl.foldUnsafe e #[] (fun n a => a.push n)
private unsafe def check (label : String) (e : Expr) : IO Unit := do
  IO.println (label ++ ":used=" ++ render e.getUsedConstants)
  IO.println (label ++ ":used-again=" ++ render e.getUsedConstants)
  IO.println (label ++ ":callback=" ++ render (observed e))
unsafe def run : IO Unit := do
  let ref ← IO.mkRef (`A : Name)
  let a ← freshConst ref
  let aAgain ← freshConst ref
  ref.set `B
  let b ← freshConst ref
  ref.set `C
  let c ← freshConst ref
  let shared := mkApp a b
  check "shared-and-equal" (mkApp shared (mkApp shared aAgain))
  let binding := Expr.forallE `x a (Expr.lam `y b c .implicit) .default
  let letValue := Expr.letE `z a b c true
  check "binding-let-mdata-proj" (.mdata {} (mkApp binding (.proj `Struct 1 letValue)))
  check "levels" (.const `UniverseConst [.param `universe])
  let leaves := #[Expr.bvar 0, .fvar ⟨`free⟩, .mvar ⟨`meta⟩, .sort (.param `u),
                  .lit (.natVal 42), .lit (.strVal "text")]
  check "nonconstant-leaves" (leaves.foldl mkApp (.sort .zero))
  let mut dag := a
  for _ in [:12] do
    dag := mkApp dag dag
  check "repeated-dag" dag
end FoldConstsOracle
unsafe def main : IO Unit := FoldConstsOracle.run
