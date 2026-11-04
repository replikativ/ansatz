set_option linter.unusedVariables false

-- Lean Elab.Tactic.Simp.simpLocation/dsimpLocation and Meta.simpGoal/dsimpGoal.
example (b c : Bool) : false = true → c = true → b = true := by
  intro h1 h2
  simp at h1 h2
example (b c : Bool) : false = true → c = true → b = true := by
  intro h1 h2
  simp at h1 ⊢
example (b c : Bool) : false = true → c = true → b = true := by
  intro h1 h2
  simp at *
example (b c : Bool) : false = true → c = true → b = true := by
  intro h1 h2
  simp only [Bool.false_eq_true] at h1 h2
example (b c : Bool) : false = true → c = true → b = true := by
  intro h1 h2
  simp_all
example (P Q : Prop) (h1 : P) (h2 : Q ∧ True) : Q := by
  simp at h1 h2
  exact h2
example (P Q : Prop) (h1 : P) (h2 : Q ∧ True) : Q := by
  simp at h2 h1
  exact h2
example (P Q : Prop) (h1 : P) (h2 : Q ∧ True) : Q := by
  simp at h1 h2 ⊢
  exact h2
example (P Q : Prop) (h1 : P) (h2 : Q ∧ True) : Q := by
  simp at *
  exact h2
example (P : Prop) (h : P) : P ∧ True := by
  simp at h ⊢
  exact h
example (P Q : Prop) (h1 : P) (h2 : Q) : P := by
  fail_if_success simp at h1 h2
  exact h1
example (h : false = true) : False := by
  fail_if_success simp at h missing
  simp at h
example (P : Prop) (h1 : False) (h2 : P) : P := by dsimp at h1 h2
example (P : Prop) (h : False) : P := by dsimp at h ⊢
example (P : Prop) (h : False) : P := by dsimp at *
example (P Q : Prop) (h1 : P) (h2 : (match true with | true => Q | false => True)) : Q := by
  dsimp at h1 h2
  guard_hyp h2 :ₛ Q
  exact h2
example (P : Prop) (h : P) : P := by
  fail_if_success dsimp at h
  exact h
example (P : Prop) (h : false = true) (hp : P) : P ∧ P := by
  constructor
  · simp at h hp
  · exact hp
example (P Q : Prop) (h1 : P ∧ True) (h2 : Q ∧ True) : P ∧ Q := by
  simp at h2 h1 ⊢
  constructor
  · exact h1
  · exact h2
example (P : Prop) (h : P ∧ True) : True ∧ True := by
  simp at h ⊢
example (P : Prop) (h1 : False) (h2 : P) : P := by dsimp only at h1 h2
example (P Q : Prop) (h1 : P) (h2 : (let R := Q; R)) : Q := by
  fail_if_success guard_hyp h2 :ₛ Q
  dsimp at h1 h2
  guard_hyp h2 :ₛ Q
  exact h2
