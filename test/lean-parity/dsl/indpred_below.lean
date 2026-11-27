/-
Pairs with: ansatz.indpred-below-test
Observed with Lean v4.36.0 (core only), Meta/IndPredBelow.lean: a recursive inductive predicate
gets `below` as an inductive predicate (one constructor per constructor, with the nested below
proof and the motive proof after each recursive argument) and `brecOn` as a theorem; no
`binductionOn`.
-/
inductive Step : Nat → Prop where
  | base : Step 0
  | next {n} (h : Step n) : Step (n + 1)
/--
info: inductive Step.below : {motive : (a : Nat) → Step a → Prop} → {a : Nat} → Step a → Prop
number of parameters: 1
constructors:
Step.below.base : ∀ {motive : (a : Nat) → Step a → Prop}, Step.below Step.base
Step.below.next : ∀ {motive : (a : Nat) → Step a → Prop} {n : Nat} (h : Step n),
  Step.below h → motive n h → Step.below ⋯
-/
#guard_msgs in #print Step.below
/--
info: @Step.brecOn : ∀ {motive : (a : Nat) → Step a → Prop} {a : Nat} (t : Step a),
  (∀ (a : Nat) (t : Step a), Step.below t → motive a t) → motive a t
-/
#guard_msgs in #check @Step.brecOn
/-- info: theorem Step.brecOn : ∀ {motive : (a : Nat) → Step a → Prop} {a : Nat} (t : Step a),
  (∀ (a : Nat) (t : Step a), Step.below t → motive a t) → motive a t :=
fun {motive} {a} t F_1 => F_1 a t (Step.rec Step.below.base (fun {n} h ih => Step.below.next h ih (F_1 n h ih)) t) -/
#guard_msgs in #print Step.brecOn
/-- error: Unknown constant `Step.binductionOn` -/
#guard_msgs in #check @Step.binductionOn
