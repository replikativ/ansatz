/-
Pairs with: ansatz.constructions-test/enum-no-confusion-follows-the-helper-telescope
Observed with Lean v4.36.0 (core only):
- the prelude helpers take two universe levels and a tag function `α → Nat` (no codomain,
  no `DecidableEq` dictionary);
- a fieldless enum with ≥ 2 constructors gets `T.noConfusionType := noConfusionTypeEnum T.ctorIdx`
  and `T.noConfusion := noConfusionEnum T.ctorIdx h`, with `{P} {x y}` implicit;
- a one-constructor enum gets `P → P` and the identity;
- the type reduces to `P` on distinct constructors and to `P → P` on equal ones.
-/
/-- info: @noConfusionTypeEnum : {α : Sort u_1} → (α → Nat) → Sort u_2 → α → α → Sort u_2 -/
#guard_msgs in #check @noConfusionTypeEnum
/--
info: @noConfusionEnum : {α : Sort u_1} → (f : α → Nat) → {P : Sort u_2} → {x y : α} → x = y → noConfusionTypeEnum f P x y
-/
#guard_msgs in #check @noConfusionEnum

inductive Color where | red | green | blue

example : @Color.noConfusionType = fun P x y => noConfusionTypeEnum Color.ctorIdx P x y := rfl
example : @Color.noConfusion = fun {P} {x y} h => @noConfusionEnum Color Color.ctorIdx P x y h := rfl
example (P : Sort u) : Color.noConfusionType P .red .blue = P := rfl
example (P : Sort u) : Color.noConfusionType P .green .green = (P → P) := rfl
example : Color.red ≠ Color.green := fun h => Color.noConfusion h

inductive Solo where | only

example : @Solo.noConfusionType = fun P (_ _ : Solo) => P → P := rfl
example : @Solo.noConfusion = fun {P} {_ _ : Solo} (_ : _ = _) (p : P) => p := rfl

/-! Sort-polymorphic enums (Lean tests/elab/issue14904.lean): with several constructors the type
eliminates only into `Prop`, so there is no `ctorIdx` and the enum shortcut does not apply; the
core construction skips it too. A single constructor keeps both. -/
set_option bootstrap.inductiveCheckResultingUniverse false

inductive Bool2 : Sort u where | yes | no

/-- error: Unknown constant `Bool2.ctorIdx` -/
#guard_msgs in #check @Bool2.ctorIdx
/-- error: Unknown constant `Bool2.noConfusion` -/
#guard_msgs in #check @Bool2.noConfusion

inductive Unit2 : Sort u where | unit

/-- info: @Unit2.noConfusion : {P : Sort u_1} → {x y : Unit2} → x = y → Unit2.noConfusionType P x y -/
#guard_msgs in #check @Unit2.noConfusion
