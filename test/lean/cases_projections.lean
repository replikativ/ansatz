-- Lean 4.33.1 references for named cases and generalization under projections.
structure FrameState where
  x : Nat
structure FrameOutcome where
  state : FrameState
  accepted : Bool

def frameStep (n : Nat) (s : FrameState) : FrameOutcome :=
  if Nat.beq n 0 then ⟨s, true⟩ else ⟨s, false⟩

theorem frame_by_cases (n : Nat) (s : FrameState) :
    (frameStep n s).state = s := by
  cases h : Nat.beq n 0 <;> simp [frameStep, h]

example (s : FrameOutcome) : s.accepted = s.accepted := by
  cases h : s.accepted
  · exact Eq.refl false
  · exact Eq.refl true

example (s : FrameOutcome) : s.state.x = s.state.x := by
  generalize h : s.state.x = x
  exact Eq.refl x

example (s : FrameState) (b : Bool) :
    (FrameOutcome.mk s (Bool.not b)).accepted = Bool.not b := by
  cases h : Bool.not b
  · exact Eq.refl false
  · exact Eq.refl true

example (n : Nat) (b : Bool) :
    (FrameOutcome.mk (FrameState.mk (Nat.succ n)) b).state.x = Nat.succ n := by
  generalize h : Nat.succ n = x
  exact Eq.refl x

example (n : Nat) (x : Fin n) : x = x := by
  fail_if_success generalize h : n = k
  rfl

example (n : Nat) (s : FrameState) : (frameStep n s).state.x = s.x := by
  cases h : Nat.beq n 0 <;> simp [frameStep, h]
