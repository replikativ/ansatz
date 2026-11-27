/-
Kernel-level admission checks, submitted with `addDecl` so the elaborator is bypassed and the
kernel's `environment::add_inductive` is what answers (K4 audit findings 7, 10, 11).
-/
import Lean
open Lean

def mkInd (n : Name) (lps : List Name) (np : Nat) (ty : Expr) (ctors : List (Name × Expr)) : CoreM Unit :=
  addDecl (.inductDecl lps np [{ name := n, type := ty, ctors := ctors.map fun (c, t) => { name := c, type := t } }] false)

/-! ## Closedness and the reserved `_nested` prefix (finding 10) -/

/-- error: (kernel) declaration has metavariables 'I1' -/
#guard_msgs in
#eval mkInd `I1 [] 0 (mkSort (.mvar ⟨`u⟩)) []

/--
error: (kernel) declaration has free variables 'I2.mk', expression: ⏎
  x → I2
-/
#guard_msgs in
#eval mkInd `I2 [] 0 (mkSort Level.one) [(`I2.mk, mkForall `a .default (mkFVar ⟨`x⟩) (mkConst `I2))]

/-- error: (kernel) invalid declaration 'I3.mk', it uses the reserved prefix '_nested' -/
#guard_msgs in
#eval mkInd `I3 [] 0 (mkSort Level.one) [(`I3.mk, mkForall `a .default (mkConst `_nested.Foo_1) (mkConst `I3))]

/-! ## Uniform occurrences are checked syntactically (finding 7)

`T.mk : (fun _ : Type => Unit) (T Nat) → T α` reduces to `Unit → T α`, but the occurrence
`T Nat` is not applied to the parameter. -/

/-- error: (kernel) invalid occurrence of datatype 'T' being declared: it must be applied to the parameters and universe levels of the mutual declaration -/
#guard_msgs in
#eval do
  let T := mkConst `T
  let redex := mkApp (mkLambda `x .default (mkSort Level.one) (mkConst `Unit)) (mkApp T (mkConst `Nat))
  mkInd `T [] 1 (mkForall `α .default (mkSort Level.one) (mkSort Level.one))
    [(`T.mk, mkForall `α .implicit (mkSort Level.one) (mkForall `a .default redex (mkApp T (mkBVar 1))))]

/-! ## The parameters of the first type must be manifest (`get_params` does not reduce) -/

def HA : Type 1 := Type → Type

/-- error: (kernel) invalid inductive datatype declaration, incorrect number of parameters -/
#guard_msgs in
#eval mkInd `I6 [] 1 (mkConst `HA) []

/-! ## Field universes use `is_geq`, mutual headers `is_equivalent` (finding 11)

With `s = imax a b`, the family `I4.{a,b,c} (P : Sort a) (Q : Sort b) : Sort (imax c s)` cannot
hold a field `P → Q : Sort s`: `is_geq_core` decomposes the smaller `imax` first. -/

def s : Level := mkLevelIMax (.param `a) (.param `b)
def hdr (l : Level) : Expr :=
  mkForall `P .default (mkSort (.param `a)) (mkForall `Q .default (mkSort (.param `b)) (mkSort l))
def ctorOver (I : Expr) (field : Expr) : Expr :=
  mkForall `P .implicit (mkSort (.param `a)) (mkForall `Q .implicit (mkSort (.param `b))
    (mkForall `f .default field (mkApp2 I (mkBVar 2) (mkBVar 1))))
/-- `P → Q` under the binders `P Q` -/
def PQ : Expr := mkForall `x .default (mkBVar 1) (mkBVar 1)

/-- error: (kernel) universe level of type_of(arg #3) of 'I4.mk' is too big for the corresponding inductive datatype -/
#guard_msgs in
#eval mkInd `I4 [`a, `b, `c] 2 (hdr (mkLevelIMax (.param `c) s))
  [(`I4.mk, ctorOver (mkConst `I4 [.param `a, .param `b, .param `c]) PQ)]

-- `(P → Q) → Q : Sort (imax s b)` fits in `Sort s`: Lean proves `s ≥ s` and `s ≥ b`.
#guard_msgs in
#eval mkInd `I5 [`a, `b] 2 (hdr s)
  [(`I5.mk, ctorOver (mkConst `I5 [.param `a, .param `b]) (mkForall `g .default PQ (mkBVar 1)))]

-- `Sort s` and `Sort (max s b)` agree for every assignment, but their normal forms differ.
/-- error: (kernel) mutually inductive types must live in the same universe -/
#guard_msgs in
#eval addDecl (.inductDecl [`a, `b] 2 [{ name := `M1, type := hdr s, ctors := [] },
                                       { name := `M2, type := hdr (mkLevelMax s (.param `b)), ctors := [] }] false)
