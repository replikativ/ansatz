/-
Pairs with: ansatz.structural-mutual-test
Observed with Lean v4.36.0 (core only), Elab/PreDefinition/Structural/BRecOn.lean:
- a mutual block is one declaration: `Tree.brecOn` takes a motive and a functional per type;
  structural recursion on `Tree` alone supplies `fun _ => PUnit` / `fun _ _ => PUnit.unit` for
  `Forest` (no function recurses on it);
- a reflexive field `k : Nat → W` gives a function-valued induction hypothesis that the
  recursive call `wleft (k 0)` instantiates;
- a nested type's brecOn takes a motive per nested occurrence.
-/
mutual
inductive Tree where | leaf | node (l : Tree) (f : Forest)
inductive Forest where | nil | cons (t : Tree) (f : Forest)
end
def depth : Tree → Nat
  | .leaf => 0
  | .node l _ => depth l + 1
termination_by structural t => t
/-- info: def depth : Tree → Nat :=
fun x => x.brecOn depth._f fun t f => PUnit.unit -/
#guard_msgs in #print depth
example : depth (.node (.node .leaf .nil) .nil) = 2 := rfl

inductive W where | leaf | branch (k : Nat → W)
def wleft : W → Nat
  | .leaf => 0
  | .branch k => wleft (k 0) + 1
termination_by structural w => w
example : wleft (.branch fun _ => .branch fun _ => .leaf) = 2 := rfl

inductive Rose where | leaf | node (cs : List Rose) (r : Rose)
def rdepth : Rose → Nat
  | .leaf => 0
  | .node _ r => rdepth r + 1
termination_by structural r => r
example : rdepth (.node [] (.node [.leaf] .leaf)) = 2 := rfl
/--
info: @Rose.brecOn : {motive_1 : Rose → Sort u_1} →
  {motive_2 : List Rose → Sort u_1} →
    (t : Rose) → ((t : Rose) → t.below → motive_1 t) → ((t : List Rose) → Rose.below_1 t → motive_2 t) → motive_1 t
-/
#guard_msgs in #check @Rose.brecOn

-- a doubly nested occurrence: one auxiliary per nested type
inductive Deep where | node (cs : List (List Deep))
/-- info: Deep.below_2 : List Deep → Type -/
#guard_msgs in #check @Deep.below_2 (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
