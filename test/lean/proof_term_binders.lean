example (b : Bool) (h : b = true) : b = true := (fun (hh : b = true) => hh) h

example (b : Bool) (h : b = true) : b = true :=
  ((fun (x : Bool) => fun (hh : x = true) => hh) b) h

example (b : Bool) (h : b = true) : b = true := let hh : b = true := h; hh

example (b : Bool) : (hh : b = true) → b = true := fun (hh : b = true) => hh

example (b : Bool) (h : b = true) : b = true := by
  exact let part := b; let hp := Eq.trans (Eq.refl part) h; hp

example (b : Bool) (h : b = true) : b = true := by
  exact (fun (x : Bool) (hx : x = true) =>
    let part := x; let hp := Eq.trans (Eq.refl part) hx; hp) b h

example (b : Bool) (h : b = true) : b = true := by
  exact let part := b; (let alias := part; let hp := Eq.trans (Eq.refl alias) h; hp)

example (b : Bool) (h : b = true) : b = true := by
  exact let part : Bool := b; let hp : part = true := Eq.trans (Eq.refl part) h; hp

def comparisonLambda (n : Nat) : Bool := (fun (x : Nat) => x == 1) n
example : comparisonLambda 1 = true := rfl
example : comparisonLambda 2 = false := rfl

def comparisonProofBinder (n : Nat) (h : n = 1) : Bool :=
  (fun (_hh : n = 1) => n == 1) h
example (n : Nat) (h : n = 1) : comparisonProofBinder n h = true := by
  simp [comparisonProofBinder, h]
