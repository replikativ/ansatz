import Lean

-- Lean v4.33.1, src/kernel/inductive.cpp: elim_only_at_universe_zero.
-- Whole result arguments expose data fields; subterms of an index do not.
set_option inductive.autoPromoteIndices false
noncomputable section

inductive ElimPair where
  | mk (a b : Nat)
inductive PairIndex : ElimPair → Prop where
  | mk (a b : Nat) : PairIndex (ElimPair.mk a b)
inductive PairProofIndex : ElimPair → Prop where
  | mk (a b : Nat) (h : a = b) : PairProofIndex (ElimPair.mk a b)
inductive ConsIndex : List Nat → Prop where
  | mk (a : Nat) (b : List Nat) : ConsIndex (a :: b)
inductive TwoPairIndex : ElimPair → Prop where
  | left (a b : Nat) : TwoPairIndex (ElimPair.mk a b)
  | right (a b : Nat) : TwoPairIndex (ElimPair.mk a b)
inductive DirectIndex : Nat → Nat → Prop where
  | refl (a : Nat) : DirectIndex a a
inductive DirectProofIndex (p : Nat → Prop) : Nat → Prop where
  | mk (a : Nat) (h : p a) : DirectProofIndex p a
inductive ProofOnly (p : Prop) : Prop where
  | mk (h : p) : ProofOnly p
inductive EmptyProp : Prop
inductive HiddenData : Prop where
  | mk (a : Nat)

-- Prop-only recursors have no motive universe parameter to instantiate.
run_meta do
  for (name, expected) in [(``PairIndex.rec, 0), (``PairProofIndex.rec, 0),
      (``ConsIndex.rec, 0), (``TwoPairIndex.rec, 0), (``HiddenData.rec, 0),
      (``DirectIndex.rec, 1), (``DirectProofIndex.rec, 1),
      (``ProofOnly.rec, 1), (``EmptyProp.rec, 1)] do
    let info ← Lean.getConstInfo name
    unless info.levelParams.length == expected do
      throwError "Unexpected recursor universe parameters for {name}"

-- These explicit type ascriptions check each recursor's motive universe.
example : ∀ (motive : ∀ c, PairIndex c → Prop),
    (∀ a b, motive (ElimPair.mk a b) (PairIndex.mk a b)) →
    ∀ c h, motive c h := @PairIndex.rec
example : ∀ (motive : ∀ c, PairProofIndex c → Prop),
    (∀ a b h, motive (ElimPair.mk a b) (PairProofIndex.mk a b h)) →
    ∀ c h, motive c h := @PairProofIndex.rec
example : ∀ (motive : ∀ c, ConsIndex c → Prop),
    (∀ a b, motive (a :: b) (ConsIndex.mk a b)) →
    ∀ c h, motive c h := @ConsIndex.rec
example : ∀ (motive : ∀ c, TwoPairIndex c → Prop),
    (∀ a b, motive (ElimPair.mk a b) (TwoPairIndex.left a b)) →
    (∀ a b, motive (ElimPair.mk a b) (TwoPairIndex.right a b)) →
    ∀ c h, motive c h := @TwoPairIndex.rec
example : ∀ (motive : ∀ a b, DirectIndex a b → Sort u),
    (∀ a, motive a a (DirectIndex.refl a)) →
    ∀ a b h, motive a b h := @DirectIndex.rec.{u}
example : ∀ (p : Nat → Prop) (motive : ∀ a, DirectProofIndex p a → Sort u),
    (∀ a h, motive a (DirectProofIndex.mk a h)) →
    ∀ a h, motive a h := @DirectProofIndex.rec.{u}
example : ∀ (p : Prop) (motive : ProofOnly p → Sort u),
    (∀ h, motive (ProofOnly.mk h)) → ∀ h, motive h := @ProofOnly.rec.{u}
example : ∀ (motive : EmptyProp → Sort u) h, motive h := @EmptyProp.rec.{u}
example : ∀ (motive : HiddenData → Prop),
    (∀ a, motive (HiddenData.mk a)) → ∀ h, motive h := @HiddenData.rec
