/-
Pairs with: ansatz.sizeof-test
Observed with Lean v4.36.0 (core only):
- every non-ignored field contributes `sizeOf field` through instance synthesis (an applied type
  such as `Option Nat` included); a recursive field contributes its induction hypothesis in
  `_sizeOf_1` and `sizeOf field` in the spec; higher-order fields are ignored except `Unit → _`;
- a type parameter gets a local `[SizeOf α]` dictionary in `_sizeOf_1`, the instance and the specs;
  the instance takes the parameters explicitly;
- indices are arguments of `_sizeOf_1` and the instance;
- structures get the same declarations;
- `SizeOf.sizeOf` evaluates with the dictionary it is given.
-/
inductive Wrap where | w (v : Option Nat)
/-- info: Wrap.w.sizeOf_spec (v : Option Nat) : sizeOf (Wrap.w v) = 1 + sizeOf v -/
#guard_msgs in #check Wrap.w.sizeOf_spec
example : sizeOf (Wrap.w (some 3)) = 5 := rfl
/-- info: Wrap._sizeOf_inst -/
#guard_msgs in #synth SizeOf Wrap

example : @SizeOf.sizeOf Nat ⟨fun _ => 37⟩ 3 = 37 := rfl
/-- info: 37 -/
#guard_msgs in #eval @SizeOf.sizeOf Nat ⟨fun _ => 37⟩ 3

inductive T2 where | leaf | node (l r : T2) (k : Nat)
example : @T2._sizeOf_1 = fun t => T2.rec 1 (fun _ _ k l_ih r_ih => 1 + l_ih + r_ih + sizeOf k) t := rfl
/--
info: T2.node.sizeOf_spec (l r : T2) (k : Nat) : sizeOf (l.node r k) = 1 + sizeOf l + sizeOf r + sizeOf k
-/
#guard_msgs in #check T2.node.sizeOf_spec

inductive Box (α : Type u) where | mk (a : α) (n : Nat)
/-- info: @Box._sizeOf_1 : {α : Type u_1} → [SizeOf α] → Box α → Nat -/
#guard_msgs in #check @Box._sizeOf_1
/-- info: Box._sizeOf_inst.{u} (α : Type u) [SizeOf α] : SizeOf (Box α) -/
#guard_msgs in #check Box._sizeOf_inst
/--
info: @Box.mk.sizeOf_spec : ∀ {α : Type u_1} [inst : SizeOf α] (a : α) (n : Nat),
  sizeOf (Box.mk a n) = 1 + sizeOf a + sizeOf n
-/
#guard_msgs in #check @Box.mk.sizeOf_spec
example : sizeOf (Box.mk (Box.mk 2 0) 1) = 5 := rfl

-- `f` (higher order) is ignored; `g : Unit → Nat` is not; `b : Bool` uses `Bool`'s instance
inductive Flag where | mk (b : Bool) (f : Nat → Nat) (g : Unit → Nat)
/--
info: Flag.mk.sizeOf_spec (b : Bool) (f : Nat → Nat) (g : Unit → Nat) : sizeOf (Flag.mk b f g) = 1 + sizeOf b + sizeOf g
-/
#guard_msgs in #check Flag.mk.sizeOf_spec
example : sizeOf (Flag.mk true id (fun _ => 4)) = 6 := rfl

structure Pos where
  n : Nat
  h : 0 < n
/-- info: Pos.mk.sizeOf_spec (n : Nat) (h : 0 < n) : sizeOf { n := n, h := h } = 1 + sizeOf n + sizeOf h -/
#guard_msgs in #check Pos.mk.sizeOf_spec
example : sizeOf (Pos.mk 3 (by decide)) = 4 := rfl

inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons {n} (x : α) (xs : V α n) : V α (n+1)
/-- info: @V._sizeOf_1 : {α : Type} → [SizeOf α] → {a : Nat} → V α a → Nat -/
#guard_msgs in #check @V._sizeOf_1
/--
info: @V.cons.sizeOf_spec : ∀ {α : Type} [inst : SizeOf α] {n : Nat} (x : α) (xs : V α n),
  sizeOf (V.cons x xs) = 1 + sizeOf n + sizeOf x + sizeOf xs
-/
#guard_msgs in #check @V.cons.sizeOf_spec
