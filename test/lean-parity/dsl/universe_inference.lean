/-
Pairs with: ansatz.universe-inference-test
Observed with Lean v4.36.0 (core only), Elab/MutualInductive.lean inferResultingUniverse /
isPropCandidate: without an explicit result sort, the resulting universe is the least `Sort`
above every constructor field (at least `Type`); a type with one constructor whose fields (at
least one) are all proofs is a `Prop`; empty and fieldless types are `Type`; an explicit result
sort is kept; universe parameters of field types become parameters of the declaration.
-/
inductive Carrier where | mk (α : Type)
/-- info: Carrier : Type 1 -/
#guard_msgs in #check Carrier

inductive Phantom (α : Type u) where | mk
/-- info: Phantom.{u} (α : Type u) : Type -/
#guard_msgs in #check Phantom

inductive Law (p : Prop) where | mk (h : p)
/-- info: Law (p : Prop) : Prop -/
#guard_msgs in #check Law

inductive Box (α : Type u) where | mk (x : α)
/-- info: Box.{u} (α : Type u) : Type u -/
#guard_msgs in #check Box

inductive Pick where | mk (α : Type u) (x : α)
/-- info: Pick.{u} : Type (u + 1) -/
#guard_msgs in #check Pick

inductive Mix (α : Type u) (β : Type v) where | mk (a : α) (b : β)
/-- info: Mix.{u, v} (α : Type u) (β : Type v) : Type (max u v) -/
#guard_msgs in #check Mix

inductive Empty2
/-- info: Empty2 : Type -/
#guard_msgs in #check Empty2
inductive Enum2 where | a | b
/-- info: Enum2 : Type -/
#guard_msgs in #check Enum2

structure PS (p q : Prop) where
  hp : p
  hq : q
/-- info: PS (p q : Prop) : Prop -/
#guard_msgs in #check PS

-- two constructors: not a Prop candidate
inductive Two (p : Prop) where | a (h : p) | b (h : p)
/-- info: Two (p : Prop) : Type -/
#guard_msgs in #check Two

-- an explicit result sort is kept
inductive Expl : Type 1 where | mk (n : Nat)
/-- info: Expl : Type 1 -/
#guard_msgs in #check Expl
