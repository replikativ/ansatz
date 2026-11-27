/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-bad-rewrite-check-does-not-reduce-recursors (raw projection)
Observed with Lean v4.36.0: the inverse of `∀ x, (Prod.mk x x).1 = x` with a raw `Expr.proj` is accepted (proj := .no).
-/
import Lean
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Lean Meta Elab Command

-- the surface would elaborate `.1` to `Prod.fst`; build the raw projection directly
run_cmd liftTermElabM do
  let nat := mkConst ``Nat
  let body := mkApp3 (mkConst ``Eq [1]) nat
    (mkProj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0]) nat nat (mkBVar 0) (mkBVar 0))) (mkBVar 0)
  addDecl (.axiomDecl { name := `proj_refl, levelParams := [], type := mkForall `x .default nat body,
                        isUnsafe := false })

run_meta do
  let _ ← ({} : SimpTheorems).addConst `proj_refl (inv := true)
