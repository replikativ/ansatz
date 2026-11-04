import Lean

example (v x : Nat) (h : v = x) : v = x := by
  subst h
  exact Eq.refl v
example (v x : Nat) (h : v = x) : v = x := by
  subst_vars
  exact Eq.refl x
example (v x : Nat) (h : v = x) : v = x := by
  subst v
  exact Eq.refl x
example (v x : Nat) (h : v = x) : v = x := by
  subst x
  exact Eq.refl v
example (v x : Nat) (h : v = (fun n => n) x) : v = x := by
  subst h
  exact Eq.refl v
example (x : Nat) (h : x = 3) : x = 3 := by
  subst h
  exact Eq.refl 3
example (P : Nat → Prop) (v x : Nat) (h : v = x) (hx : P x) : P v := by
  subst h
  exact hx
example (x : Nat) (hbad : x = x + 1) (hgood : x = 3) : x = 3 := by
  subst x
  exact Eq.refl 3
example (x : Nat) (hbad : x = x + 1) (hgood : x = 3) : x = 3 := by
  subst_vars
  exact Eq.refl 3
