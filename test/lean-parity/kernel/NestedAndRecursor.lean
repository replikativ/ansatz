/-
Nested-occurrence identity and generated recursor shape.
-/
import Lean
open Lean

/-! ## Nested occurrences are identified up to binder names (completeness table)

`C (fun x => x) T` and `C (fun y => y) T` are one nested occurrence: one auxiliary type, so
`T.rec` has two motives and `numNested = 1`. -/

inductive C (f : Nat → Nat) (α : Type) where
  | mk : α → C f α

#guard_msgs in
#eval show CoreM Unit from do
  let T := mkConst `T
  let idx := mkLambda `x .default (mkConst `Nat) (mkBVar 0)
  let idy := mkLambda `y .default (mkConst `Nat) (mkBVar 0)
  let ty := mkForall `a .default (mkApp2 (mkConst `C) idx T) (mkForall `b .default (mkApp2 (mkConst `C) idy T) T)
  addDecl (.inductDecl [] 0 [{ name := `T, type := mkSort Level.one, ctors := [{ name := `T.node, type := ty }] }] false)

/-- info: numNested = 1, numMotives = 2 -/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let some (.inductInfo i) := env.find? `T | throwError "no T"
  let some (.recInfo r) := env.find? `T.rec | throwError "no T.rec"
  logInfo m!"numNested = {i.numNested}, numMotives = {r.numMotives}"

/-! ## Recursor binders: strict `infer_implicit`

The motive of an empty proposition occurs in no later explicit domain, so it stays explicit;
`False.rec`'s motive is explicit for the same reason. -/

inductive E : Prop

/-- info: E.rec.{u} (motive : E → Sort u) (t : E) : motive t -/
#guard_msgs in
#check E.rec

/-! ## Empty propositions eliminate into any universe; data-carrying ones only into Prop -/

inductive P1 : Prop where
  | mk : Nat → P1

/-- info: P1.rec {motive : P1 → Prop} (mk : ∀ (a : Nat), motive ⋯) (t : P1) : motive t -/
#guard_msgs in
#check P1.rec

/-! ## Auxiliary recursors of a nested type are named `<first>.rec_<i>` -/

inductive Tree where
  | node : List Tree → Tree

/-- info: numNested = 1, Tree.rec_1 rules = [List.nil, List.cons] -/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let some (.inductInfo i) := env.find? `Tree | throwError "no Tree"
  let some (.recInfo r) := env.find? `Tree.rec_1 | throwError "no Tree.rec_1"
  logInfo m!"numNested = {i.numNested}, Tree.rec_1 rules = {r.rules.map (·.ctor)}"
