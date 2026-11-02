import Lean
open Lean Meta
#eval toString (appendTag `main (.str .anonymous "001"))
#eval repr (appendTag `main (.str .anonymous "001"))
#eval toString (appendTag `main (addMacroScope `Review `h 42))
#eval repr (appendTag (addMacroScope `Review `main 42) `h)
#eval repr (addMacroScope `Review `main 42)
open Elab Tactic
elab "set_main_tag" : tactic => do (← getMainGoal).setTag `main
example (f : («001» : True) → (hb : True) → True) : True := by
  set_main_tag
  apply f
  case «001» => trivial
  case hb => trivial
example (f : («9223372036854775808» : True) → (hb : True) → True) : True := by
  set_main_tag
  apply f
  case «9223372036854775808» => trivial
  case hb => trivial

#guard appendTag `main (.str .anonymous "001") == .str `main "001"
#guard appendTag `main (.str .anonymous "9223372036854775808") ==
  .str `main "9223372036854775808"
#guard appendTag `main (.str .anonymous "literal.dot") == .str `main "literal.dot"
#guard appendTag `main (addMacroScope `X `h 42) == `main.h
#guard appendTag (addMacroScope `X `main 42) (addMacroScope `Y `h 17) ==
  addMacroScope `X `main.h 42
