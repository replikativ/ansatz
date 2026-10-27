-- Compiler regression fixtures. The corresponding runtime differential tests use
-- these kernel-checked recursors, including mk_rec_rules' lambda-wrapped IHs.
inductive ReviewHigher where
  | leaf : Nat → ReviewHigher
  | node : (Nat → ReviewHigher) → ReviewHigher

noncomputable def reviewHigher (t : ReviewHigher) : Nat :=
  ReviewHigher.rec (fun n => n) (fun _ ih => ih 0) t

theorem reviewHigher_kernel :
    reviewHigher (.node (fun _ => .leaf 7)) = 7 := rfl

inductive CGHigherLeaf where
  | leaf : CGHigherLeaf
  | node : (Nat → CGHigherLeaf) → CGHigherLeaf

inductive CGHigherTagged where
  | leaf : Nat → CGHigherTagged
  | node : (Nat → Nat → CGHigherTagged) → CGHigherTagged
  | «end» : CGHigherTagged

inductive CGHigherSingle where
  | mk : (Empty → CGHigherSingle) → CGHigherSingle

inductive CGHigherIx : Nat → Type where
  | leaf (k payload : Nat) : CGHigherIx k
  | node (k : Nat) (f : Nat → CGHigherIx k) : CGHigherIx k

-- Unlike CGHigherIx, this varying index cannot become a uniform parameter.
inductive CGHigherIndexed : Nat → Type where
  | leaf (k payload : Nat) : CGHigherIndexed k
  | node (k : Nat) (f : Nat → CGHigherIndexed k) : CGHigherIndexed (Nat.succ k)
