# Match compiler and tactic campaign

The implementation should follow `../lean4/src/Lean/Meta/Match` and Lean's tactic
code where practical. Every compiler generated declaration and tactic proof must
pass the Ansatz kernel. Reproduce failures with small cases before changing the
implementation, then check the corresponding Klara proof where one exists.

| Order | Work | Lean reference | Completion check |
| --- | --- | --- | --- |
| 1 | On demand equations, precedence guards, and a distinct overlapping splitter | `MatchEqs.lean`, `Match.lean`, `SolveOverlap.lean` | Kernel checked Nat and inductive overlap proofs; existing matcher suite passes. Implemented in draft PR #238. |
| 2 | Finish `split` support for multiple discriminants and nested matches | `MatchEqs.lean` `applyMatchSplitter`, matcher input reconstruction | Equations and splitter work for multiple discriminants, overlapping arms, and nested wildcards; Klara `datumEq` and `primApply` no longer warn. |
| 3 | Reject invalid `obtain` and `cases` proofs at tactic time | `RCases.lean`, `Cases.lean`, `UnifyEq.lean` | S5 reports #7 and #8 reproduce as tactic errors; successful cases remain kernel checked. Local fixes and regressions are in progress. |
| 4 | Reduce wasted `apply` work across many induction goals | `Apply.lean` | The S5 `ev-ok` candidate search finishes in a practical time while selecting the same lemmas. |
| 5 | Reduce beta redexes left by `simp` | `Meta/Tactic/Simp/Main.lean` | S5 `smn-step2` and `run-quote` rewrite without their `simp only` workaround. |
| 6 | Recognize structural recursion when a non matched argument changes, and when a recursive call is a match scrutinee | Lean's structural recursion elaboration and `brecOn` | Klara `subst` and `ev` can be expressed with their natural argument order; S2 reports #2 and #3 pass without helper functions. |
| 7 | End to end validation | Ansatz and Klara suites | Full Ansatz suite passes outside socket restricted tests; Klara specification checks pass with removed workarounds. |

The order permits independent tactic repairs after the current splitter work.
Do not close a report because a workaround passes: its original reproduction
must pass or fail cleanly as appropriate.
