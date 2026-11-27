/-
Kernel reduction and definitional equality (K2), observed through `Lean.Kernel.whnf` and
`Lean.Kernel.isDefEq`, i.e. Lean v4.36.0's `type_checker::whnf` and `is_def_eq` directly.
Paired with test/ansatz/kernel_reduction_test.clj.
-/
import Lean
open Lean

def kwhnf (e : Expr) : CoreM Unit := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok r => logInfo m!"{r}"
  | .error _ => logInfo m!"kernel error"

def kdefeq (a b : Expr) : CoreM Unit := do
  match Kernel.isDefEq (← getEnv) {} a b with
  | .ok r => logInfo m!"{r}"
  | .error _ => logInfo m!"kernel error"

structure S where x : Nat
structure T where x : Nat
axiom ax : S

/-! ## Projections are owner-checked (`reduce_proj_core`, projection congruence) -/

/-- info: { x := 1 }.1 -/
#guard_msgs in
#eval kwhnf (.proj ``S 0 (mkApp (mkConst ``T.mk) (mkNatLit 1)))

/-- info: false -/
#guard_msgs in
#eval kdefeq (.proj ``S 0 (mkConst ``ax)) (.proj ``T 0 (mkConst ``ax))

/-! ## Nat primitives: complete constants, count and size limits (`reduce_nat`) -/

-- `Nat.add.{0}` is not the primitive `Nat.add` (and has the wrong universe arity to unfold)
/-- info: @Nat.add 2 3 -/
#guard_msgs in
#eval kwhnf (mkApp2 (mkConst ``Nat.add [Level.zero]) (mkRawNatLit 2) (mkRawNatLit 3))

-- the exponent must fit in 32 bits, even for base 1 (`get_count_arg` runs first)
/-- info: kernel error -/
#guard_msgs in
#eval kwhnf (mkApp2 (mkConst ``Nat.pow) (mkRawNatLit 1) (mkRawNatLit 4294967296))

-- `Nat.shiftRight` has no count limit
/-- info: 0 -/
#guard_msgs in
#eval kwhnf (mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit 1) (mkRawNatLit 4294967296))

-- `Nat.zero.{0}` is not `Nat.zero`: the comparison infers it and fails on the universe arity
/-- info: kernel error -/
#guard_msgs in
#eval kdefeq (mkConst ``Nat.zero [Level.zero]) (mkRawNatLit 0)

/-! ## Int is reduced through its definitions (no native Int arithmetic) -/

/-- info: Int.rec (fun a => (fun a => (fun n => Int.negOfNat n) a) a) (fun a => (fun a => (fun n => ↑n.succ) a) a) 3 -/
#guard_msgs in
#eval kwhnf (mkApp (mkConst ``Int.neg) (mkRawNatLit 3))

/-! ## Errors propagate out of proof irrelevance (`is_def_eq_proof_irrel` infers both sides) -/

/-- info: kernel error -/
#guard_msgs in
#eval kdefeq (mkConst `Unknown [Level.zero]) (mkConst `Unknown [mkLevelMax Level.zero Level.zero])

/-! ## Lazy delta has no step cutoff -/

#guard_msgs in
#eval show CoreM Unit from do
  addDecl (.defnDecl { name := `alias0, levelParams := [], type := mkConst ``Nat, value := mkConst ``Nat.zero,
                       hints := .regular 1, safety := .safe })
  for i in [1:10002] do
    addDecl (.defnDecl { name := Name.mkSimple s!"alias{i}", levelParams := [], type := mkConst ``Nat,
                         value := mkConst (Name.mkSimple s!"alias{i-1}"), hints := .regular (i+1).toUInt32, safety := .safe })

/-- info: true -/
#guard_msgs in
#eval kdefeq (mkConst `alias10001) (mkConst ``Nat.zero)
