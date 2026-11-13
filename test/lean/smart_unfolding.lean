-- Lean pair for test/ansatz/tactic/smart_unfolding_test.clj (Lean v4.33.1).
-- A structurally recursive function whose recursive call takes a nested `match` on a
-- non-structural argument: its equation theorems are split per constructor of `best`, so
-- none applies while `best` is a variable. `simp only [pick]` still unfolds one step through
-- the smart-unfolding definition (Simp.unfoldEvenWithEqns), and `unfold` rewrites with eq_def.

def pick (best : Option Nat) : List Nat → Option Nat
  | [] => best
  | h :: t => pick (match best with
                    | none => some h
                    | some b => if Nat.blt h b then some h else best) t

#check @pick.eq_2   -- pick none (h :: t) = pick (some h) t
#check @pick.eq_3   -- pick (some b) (h :: t) = pick (if h.blt b = true then some h else some b) t
#check @pick.eq_def

-- simp only unfolds through pick._sunfold; the nested match on `best` stays.
example (best : Option Nat) (h : Nat) (t : List Nat) :
    pick best (h :: t) = pick (match best with
                               | none => some h
                               | some b => if Nat.blt h b then some h else best) t := by
  simp only [pick]

-- (a statement's own `match` is a different matcher, so the shape is checked in the Clojure test)
example (best : Option Nat) (h : Nat) (t : List Nat) (e : Nat)
    (hh : pick best (h :: t) = some e) : True := by
  simp only [pick] at hh
  trivial

-- A stuck structural argument: smart unfolding fails, so simp makes no progress.
example (best : Option Nat) (es : List Nat) (e : Nat) (hh : pick best es = some e) : True := by
  fail_if_success simp only [pick] at hh
  trivial

-- The equation that does apply is still used.
example (h : Nat) (t : List Nat) : pick none (h :: t) = pick (some h) t := by
  simp only [pick]

-- unfold at a hypothesis rewrites with eq_def, then reduces the matcher when it can.
example (best : Option Nat) (h : Nat) (t : List Nat) (e : Nat)
    (hh : pick best (h :: t) = some e) : True := by
  unfold pick at hh
  trivial

-- with a variable structural argument, unfold leaves `match es with ...`
example (best : Option Nat) (es : List Nat) (e : Nat) (hh : pick best es = some e) : True := by
  unfold pick at hh
  trivial

example (best : Option Nat) : pick best [] = best := by
  unfold pick
  rfl

-- rw has no unfold fallback: no split equation matches.
example (best : Option Nat) (h : Nat) (t : List Nat) (e : Nat)
    (hh : pick best (h :: t) = some e) : True := by
  fail_if_success rw [pick] at hh
  trivial
