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

/-! ## A delta candidate needs its universe arity (`is_delta`) -/

-- `kg` (added unchecked) unfolds to `kf.{0}`, a wrong-arity application: no delta candidate, so
-- the comparison falls through to `is_def_eq_unit_like`, whose inference rejects it.
#guard_msgs in
#eval show CoreM Unit from do
  addDecl (.defnDecl { name := `kf, levelParams := [], type := mkConst ``Nat, value := mkConst ``Nat.zero,
                       hints := .regular 5, safety := .safe })
  let kg : Declaration := .defnDecl {
        name := `kg, levelParams := [], type := mkConst ``Nat,
        value := mkConst `kf [Level.zero], hints := .regular 1, safety := .safe }
  match (← getEnv).addDeclCore 0 0 kg none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "addDeclCore failed"

/-- info: kernel error -/
#guard_msgs in
#eval kdefeq (mkConst `kg) (mkConst ``Nat.zero)

/-! ## Bound variable indices are bounded (`Expr.mkData`) -/

/-- info: 1048575 -/
#guard_msgs in
#eval (Expr.bvar 1048574).looseBVarRange

/-! ## `reduce_proj_core` looks the constructor head up with `env.get` -/

/-- info: kernel error -/
#guard_msgs in
#eval kwhnf (.proj ``S 0 (mkConst `Missing))

/-! ## A nested comparison keeps the outer lazy-delta pair -/

axiom ka : Nat
noncomputable def kb : Nat := ka
axiom kh : ka = kb

-- `q` K-reduces to `ka` (comparing `ka = kb` with `ka = ka` on the way); `Nat.succ q` is not `ka`
noncomputable def q : Nat := @Eq.rec Nat ka (fun _ _ => Nat) ka kb kh

/-- info: true -/
#guard_msgs in
#eval kdefeq (mkConst ``q) (mkConst ``ka)

/-- info: false -/
#guard_msgs in
#eval kdefeq (mkApp (mkConst ``Nat.succ) (mkApp6 (mkConst ``Eq.rec [1, 1]) (mkConst ``Nat) (mkConst ``ka)
  (.lam `x (mkConst ``Nat) (.lam `h (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``ka) (.bvar 0))
    (mkConst ``Nat) .default) .default) (mkConst ``ka) (mkConst ``kb) (mkConst ``kh))) (mkConst ``ka)

/-! ## String literals expand by code point -/

def charList (cps : List Nat) : Expr :=
  cps.foldr (fun cp acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char)
    (mkApp (mkConst ``Char.ofNat) (mkRawNatLit cp)) acc) (mkApp (mkConst ``List.nil [0]) (mkConst ``Char))

/-- info: true -/
#guard_msgs in
#eval kdefeq (mkStrLit "𝔸") (mkApp (mkConst ``String.ofList) (charList [120120]))

/-- info: false -/
#guard_msgs in
#eval kdefeq (mkStrLit "𝔸") (mkApp (mkConst ``String.ofList) (charList [55349, 56632]))

/-! ## An inference error reached through `try_eta_struct_core` after unfolding -/

#guard_msgs in
#eval show CoreM Unit from do
  addDecl (.defnDecl { name := `kfS, levelParams := [], type := mkConst ``S,
                       value := mkApp (mkConst ``S.mk) (mkRawNatLit 0), hints := .regular 5, safety := .safe })
  let kgS : Declaration := .defnDecl {
        name := `kgS, levelParams := [], type := mkConst ``S,
        value := mkConst `kfS [Level.zero], hints := .regular 1, safety := .safe }
  match (← getEnv).addDeclCore 0 0 kgS none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "addDeclCore failed"

/-- info: kernel error -/
#guard_msgs in
#eval kdefeq (mkConst `kgS) (mkApp (mkConst ``S.mk) (mkRawNatLit 1))

/-! ## Deliberate divergence: a projection index that wraps Lean's unsigned sum

`0xfffffffe` passes `to_proj_idx`; with `Prod`'s two parameters `nparams + idx` wraps to 0, so
Lean's raw `reduce_proj_core` returns parameter 0. Ansatz leaves the projection stuck (see
doc/kernel.md); `infer_proj` rejects it in both kernels. -/

/-- info: Nat -/
#guard_msgs in
#eval kwhnf (.proj ``Prod 0xfffffffe (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  (mkRawNatLit 1) (mkRawNatLit 2)))
