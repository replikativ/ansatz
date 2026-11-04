import Lean
set_option linter.unusedSimpArgs false

example (h : True) : True := by
  fail_if_success simp [no_such_lemma]
  fail_if_success simp only [no_such_lemma]
  fail_if_success simp_all [no_such_lemma]
  fail_if_success simp_all only [no_such_lemma]
  fail_if_success dsimp [no_such_lemma]
  fail_if_success dsimp only [no_such_lemma]
  fail_if_success dsimp [no_such_lemma] at h
  fail_if_success dsimp only [no_such_lemma] at h
  fail_if_success simp [no_such_lemma] at h
  fail_if_success simp only [no_such_lemma] at h
  exact h
example (n : Nat) : n = n := by
  simp only [Nat.add_zero]
example (n : Nat) : n = n := by
  simp only [Nat.add_eq]
example (n : Nat) : n = n := by
  simp only [Nat.le_eq]
