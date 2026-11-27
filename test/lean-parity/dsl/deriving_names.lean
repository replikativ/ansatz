/-
Pairs with: ansatz.deriving-test/deriving-names-and-parameters
Observed with Lean v4.36.0 (core only), Elab/Deriving/DecEq.lean:
- `N.Color deriving DecidableEq` is `N.instDecidableEqColor` (the namespace of the type, then
  `instDecidableEq` and the type's last component), registered as an instance;
- an enum also gets `N.Color.ofNat` (a `bif n.ble i` chain) and `N.Color.ofNat_ctorIdx`;
- a parameterized fieldless type derives at its applied parameters, with `[DecidableEq α]` for
  each type parameter and the type's universe parameters.
-/
namespace N
inductive Color where | red | green | blue
deriving DecidableEq
end N
/-- info: N.instDecidableEqColor : DecidableEq N.Color -/
#guard_msgs in #check @N.instDecidableEqColor
/-- info: N.Color.ofNat : Nat → N.Color -/
#guard_msgs in #check @N.Color.ofNat
/-- info: N.Color.ofNat_ctorIdx : ∀ (x : N.Color), N.Color.ofNat x.ctorIdx = x -/
#guard_msgs in #check @N.Color.ofNat_ctorIdx
example : @N.Color.ofNat = fun n => bif n.ble 0 then N.Color.red else bif n.ble 1 then N.Color.green else N.Color.blue := rfl
example : decide (N.Color.red = N.Color.blue) = false := rfl

inductive P (α : Type) where | a | b
deriving DecidableEq
/-- info: @instDecidableEqP : {α : Type} → [DecidableEq α] → DecidableEq (P α) -/
#guard_msgs in #check @instDecidableEqP
example : decide (P.a (α := Nat) = P.b) = false := rfl

inductive Q.{u} (α : Sort u) where | a | b
deriving DecidableEq
/-- info: @instDecidableEqQ : {α : Sort u_1} → [DecidableEq α] → DecidableEq (Q α) -/
#guard_msgs in #check @instDecidableEqQ

-- ofNat is a balanced lookup tree (Meta/NatTable.lean); the first letter is capitalized; an
-- empty type derives the instance but is no enumeration
inductive Four where | a | b | c | d
deriving DecidableEq
example : @Four.ofNat = fun n => bif n.ble 1 then (bif n.ble 0 then Four.a else Four.b)
                                 else (bif n.ble 2 then Four.c else Four.d) := rfl
namespace M
inductive color where | x | y
deriving DecidableEq
end M
/-- info: M.instDecidableEqColor : DecidableEq M.color -/
#guard_msgs in #check @M.instDecidableEqColor
inductive Empty2 : Type
deriving DecidableEq
/-- error: Unknown constant `Empty2.ofNat` -/
#guard_msgs in #check @Empty2.ofNat
