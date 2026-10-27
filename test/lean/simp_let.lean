-- Simplifier rewrite substitution must descend through let values, types and bodies.
example (A : Type) (x : A) : (let T := A; let y : A := x; let _z : T := y; x) = x := by
  simp

namespace FrameLets
structure FrameState where
  stable : Bool
  kept : Bool
  extra : Bool

def nestedPredicate (b : Bool) : Bool :=
  let f := fun x : Bool => x
  let y := f b
  y

def frameStep (s : FrameState) (_ : Nat) : FrameState :=
  ⟨s.stable, s.kept, false⟩

theorem local_frame (s : FrameState) (id : Nat) :
    (frameStep s id).stable = s.stable := rfl

theorem kept_preserved (s : FrameState) (id : Nat) :
    s.kept = true → (frameStep s id).kept = true := by
  intro h
  exact h

theorem projection_frame (s t : FrameState) (h : s = t) : s.stable = t.stable := by
  simp only [h]

def flatInv (s : FrameState) : Bool :=
  nestedPredicate s.stable && (nestedPredicate s.stable &&
    (nestedPredicate s.stable && (nestedPredicate s.stable &&
      (nestedPredicate s.stable && (nestedPredicate s.stable &&
        (nestedPredicate s.stable && s.kept))))))

set_option linter.unusedSimpArgs false in
theorem flat_preserved (s : FrameState) (id : Nat) :
    flatInv s = true → flatInv (frameStep s id) = true := by
  intro hs
  simp_all [flatInv, local_frame, kept_preserved]
end FrameLets

-- Logical counterpart of the invariant with seven frame lemmas and one
-- preservation lemma, abstracting the downstream model's predicates.
set_option linter.unusedSimpArgs false
namespace Conjunction
variable {S : Type}
variable (p1 p2 p3 p4 p5 p6 p7 p8 : S → Bool) (step : S → Nat → S)
def flatInv (s : S) : Bool :=
  p1 s && (p2 s && (p3 s && (p4 s && (p5 s && (p6 s && (p7 s && p8 s))))))
theorem preserve
    (f1 : ∀ s i, p1 (step s i) = p1 s)
    (f2 : ∀ s i, p2 (step s i) = p2 s)
    (f3 : ∀ s i, p3 (step s i) = p3 s)
    (f4 : ∀ s i, p4 (step s i) = p4 s)
    (f5 : ∀ s i, p5 (step s i) = p5 s)
    (f6 : ∀ s i, p6 (step s i) = p6 s)
    (f7 : ∀ s i, p7 (step s i) = p7 s)
    (f8 : ∀ s i, p8 s = true → p8 (step s i) = true)
    (s : S) (i : Nat) :
    flatInv p1 p2 p3 p4 p5 p6 p7 p8 s = true →
    flatInv p1 p2 p3 p4 p5 p6 p7 p8 (step s i) = true := by
  intro hs
  simp_all [flatInv, f1, f2, f3, f4, f5, f6, f7, f8]
end Conjunction
