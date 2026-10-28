# Match compiler and tactic campaign

The implementation should follow `../lean4/src/Lean/Meta/Match` and Lean's tactic
code where practical. Every compiler generated declaration and tactic proof must
pass the Ansatz kernel. Reproduce failures with small cases before changing the
implementation, then check the corresponding Klara proof where one exists.

| Order | Work | Lean reference | Completion check |
| --- | --- | --- | --- |
| 1 | On demand equations, precedence guards, and a distinct overlapping splitter | `MatchEqs.lean`, `Match.lean`, `SolveOverlap.lean` | Kernel checked Nat and inductive overlap proofs; existing matcher suite passes. Implemented in draft PR #238. |
| 2 | Finish `split` support for multiple discriminants and nested matches | `MatchEqs.lean` `applyMatchSplitter`, matcher input reconstruction | Implemented in draft PR #238. Klara `datumEq` and `primApply` generated kernel checked equations with `*lean-matchers*` enabled. |
| 3 | Reject invalid `obtain` and `cases` proofs at tactic time | `RCases.lean`, `Cases.lean`, `UnifyEq.lean` | Implemented with regressions in draft PR #239; both invalid proofs now fail at tactic time. |
| 4 | Reduce wasted `apply` work across many induction goals | `Apply.lean` | Implemented in draft PR #239. REPL probe: 20 wrong candidates fell from 26 seconds to about 2 seconds; CI passed. |
| 5 | Reduce beta redexes left by `simp` | `Meta/Tactic/Simp/Main.lean` | Implemented in draft PR #239. Alternate `smn-step2` and `run-quote` proofs passed the Klara REPL with the default compiler; CI passed. With opt-in matchers, `smn-step2` also proves if `rw [rx]` precedes `simp only [ev]`. The original tactic order remains a migration issue. |
| 6 | Recognize structural recursion when a non matched argument changes, and when a recursive call is a match scrutinee | `Elab/PreDefinition/Structural/FixedParams.lean`, `BRecOn.lean` | Kernel checked REPL definitions cover both cases. Generated constructor equations reduce to direct recursive calls, including under a nested match. Focused tests passed before the equation change; CI pending. |
| 7 | End to end validation | Ansatz and Klara suites | The combined matcher/tactic branch passed CI at `fe6069c`; later recursion commits await CI. The full opt-in Klara specification kernel checked with an `smn-step2` proof migration. Draft Klara PR #1 tries `rw [rx]` before and after `simp only [ev]`; that theorem kernel checked with both compiler modes. |

The opt-in Klara run initially stopped at `handleEff-ok`: `simp [handleEff]`
exposed `Option.casesOn`, which `simp` did not reduce. A local fix unfolds
`*.casesOn` definitions; the REPL then reached `smn-step2`.

The generalized recursor now yields constructor-specific equations. Klara's
`smn-step2` proof migration is in draft PR #1.

The order permits independent tactic repairs after the current splitter work.
Do not close a report because a workaround passes: its original reproduction
must pass or fail cleanly as appropriate.
