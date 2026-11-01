import ExprMVarsProbe

def main : IO Unit := do
  for seed in #[0, 7] do
    for (label, actual, expected) in #[
      ("direct", ExprMVarsProbe.directSummary seed, seed + 11),
      ("delayed", ExprMVarsProbe.delayedSummary seed, seed + 11),
      ("cut", ExprMVarsProbe.cutSummary seed, seed + 111)] do
      unless actual == expected do
        throw <| IO.userError s!"{label} native canary failed: {actual}, expected {expected}"
      IO.println (Lean.Json.mkObj [("case", Lean.toJson label), ("seed", Lean.toJson seed),
                                  ("result", Lean.toJson actual)]).compress
