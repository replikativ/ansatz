(ns ansatz.tactic.grind
  "Logical refutation automation following Lean Grind/Main.lean and Finish.lean.
   The proof-producing engine lives in grind.main; optimizer graph APIs remain
   in grind.egraph. Arithmetic and ring solvers are separate follow-up work.")

(defn grind
  "Prove the open goals using branch-local congruence, propagation, E-matching
   and case splitting. Definition hints expand through their equation inventory."
  ([ps] ((requiring-resolve 'ansatz.tactic.grind.main/grind) ps))
  ([ps hints] ((requiring-resolve 'ansatz.tactic.grind.main/grind) ps hints))
  ([ps hints options] ((requiring-resolve 'ansatz.tactic.grind.main/grind) ps hints options)))

(defn grind_v2
  "Compatibility entry point for the former experimental engine."
  ([ps] (grind ps))
  ([ps hints] (grind ps hints))
  ([ps hints options] (grind ps hints options)))
