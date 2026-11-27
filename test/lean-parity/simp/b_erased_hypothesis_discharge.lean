/-
Ansatz test: ansatz.tactic.simp-pre-test/an-erased-hypothesis-does-not-discharge-a-condition
Observed with Lean v4.36.0: `simp_all only [cond_ax]` closes `F a = G a` using `h : P a`; with `-h` it makes no progress.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque F : Nat → Nat
opaque G : Nat → Nat
opaque a : Nat
axiom cond_ax : P a → F a = G a

example (h : P a) : F a = G a := by simp_all only [cond_ax]

/-- error: simp_all made no progress -/
#guard_msgs in
example (h : P a) : F a = G a := by simp_all only [cond_ax, -h]
