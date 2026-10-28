# Match compiler and tactic campaign

The implementation should follow `../lean4/src/Lean/Meta/Match` and Lean's tactic
code where practical. Every compiler generated declaration and tactic proof must
pass the Ansatz kernel. Reproduce failures with small cases before changing the
implementation, then check the corresponding Klara proof where one exists.

| Order | Work | Lean reference | Completion check |
| --- | --- | --- | --- |
| 1 | On demand equations, precedence guards, and a distinct overlapping splitter | `MatchEqs.lean`, `Match.lean`, `SolveOverlap.lean` | Merged in PR #238. Named discriminant equations and their splitter are kernel checked against imported `Nat.decEq.match_1`. |
| 2 | Finish `split` support for multiple discriminants and nested matches | `MatchEqs.lean` `applyMatchSplitter`, matcher input reconstruction | Merged in PR #238. Klara `datumEq` and `primApply` generated kernel checked equations with `*lean-matchers*` enabled. |
| 3 | Reject invalid `obtain` and `cases` proofs at tactic time | `RCases.lean`, `Cases.lean`, `UnifyEq.lean` | Merged in PR #239; both invalid proofs now fail at tactic time. |
| 4 | Reduce wasted `apply` work across many induction goals | `Apply.lean` | Merged in PR #239. REPL probe: 20 wrong candidates fell from 26 seconds to about 2 seconds. |
| 5 | Reduce beta redexes left by `simp` | `Meta/Tactic/Simp/Main.lean` | Merged in PR #239. Alternate `smn-step2` and `run-quote` proofs passed the Klara REPL with the default compiler. With opt-in matchers, `smn-step2` also proves if `rw [rx]` precedes `simp only [ev]`. The original tactic order remains a migration issue. |
| 6 | Recognize structural recursion when a non matched argument changes, and when a recursive call is a match scrutinee | `Elab/PreDefinition/Structural/FixedParams.lean`, `BRecOn.lean` | Merged in PR #239. Kernel checked regressions cover both cases, including a nested match scrutinee. In REPL, the actual 23 constructor Klara `substF` and `ev` bodies compiled in natural argument order as `substNatural` and `evNatural`; each generated 23 checked constructor equations with zero equation errors. |
| 7 | End to end validation | Ansatz and Klara suites | The combined matcher/tactic and recursion branch passed CI in PR #239. The exact Klara draft PR #1 source loaded and kernel checked the full specification with the default compiler. The full opt-in specification kernel checked with its `smn-step2` rewrite moved before `simp only [ev]`; the PR's guarded rewrite form kernel checked separately with both compiler modes. |
| 8 | Generalize matcher discriminants by argument position and simplify branch equations | `Meta/Tactic/Split.lean` `generalizeMatchDiscrs`, `Cases.unifyEqs?` | A repeated discriminant must produce independent branch equalities; unrelated occurrences in the goal must remain in place; impossible branches close before tactics run. |
| 9 | Transport named discriminant alternative binders during generalization | `Meta/Tactic/Split.lean` `withNewAltEqs` | Splitting a matcher with a nonvariable named discriminant must produce a kernel checked proof without rewriting unrelated goal occurrences. |
| 10 | Separate structural recursion from match expression compilation | `Elab/PreDefinition/Structural/{FixedParams,BRecOn,Main}.lean` | Recursion through nested matches, changing parameters, and a recursive match scrutinee uses a checked `brecOn` term whose match bodies use `Meta.Match.mkMatcher`. |
| 11 | Retire the direct recursor match compiler and enable matcher compilation by default | `Elab/Match.lean`, `Meta/Match` | Remove `compile-match-term` and the recursion-triggered matcher bypass; run the exact Ansatz and Klara regressions, including the original `smn-step2` tactic order, with the sole compiler. |

The opt-in Klara run initially stopped at `handleEff-ok`: `simp [handleEff]`
exposed `Option.casesOn`, which `simp` did not reduce. A local fix unfolds
`*.casesOn` definitions; the REPL then reached `smn-step2`.

The generalized recursor now yields constructor-specific equations. Klara's
`smn-step2` proof migration is in draft PR #1.

Do not close a report because a workaround passes: its original reproduction
must pass or fail cleanly as appropriate.
