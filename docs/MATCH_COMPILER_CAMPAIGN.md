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
| 5 | Reduce beta redexes left by `simp` | `Meta/Tactic/Simp/Main.lean` | Merged in PR #239. A later Lean-faithful no-change `simp` fix lets the original `smn-step2` and `run-quote` proof order pass with matcher compilation enabled by default. |
| 6 | Recognize structural recursion when a non matched argument changes, and when a recursive call is a match scrutinee | `Elab/PreDefinition/Structural/FixedParams.lean`, `BRecOn.lean` | Merged in PR #239. Kernel checked regressions cover both cases, including a nested match scrutinee. In REPL, the actual 23 constructor Klara `substF` and `ev` bodies compiled in natural argument order as `substNatural` and `evNatural`; each generated 23 checked constructor equations with zero equation errors. |
| 7 | End to end validation | Ansatz and Klara suites | The combined matcher/tactic and recursion branch passed CI in PR #239. The exact Klara draft PR #1 source loaded and kernel checked the full specification with the default compiler. The full opt-in specification kernel checked with its `smn-step2` rewrite moved before `simp only [ev]`; the PR's guarded rewrite form kernel checked separately with both compiler modes. |
| 8 | Generalize matcher discriminants by argument position and simplify branch equations | `Meta/Tactic/Split.lean` `generalizeMatchDiscrs`, `Cases.unifyEqs?` | Merged in PR #242. Repeated discriminants produce independent branch equalities; unrelated goal occurrences stay in place; constructor-injected equalities are processed before returning goals. |
| 9 | Transport named discriminant alternative binders during generalization | `Meta/Tactic/Split.lean` `withNewAltEqs` | Merged in PR #243. Imported `Nat.decEq.match_1` splits with a computed discriminant and kernel checks; `HEq.rec` composition is kernel checked. An integrated dependent named-discriminant split remains a coverage gap. |
| 10 | Separate structural recursion from match expression compilation | `Elab/PreDefinition/{FixedParams,Structural/BRecOn,Structural/Main}.lean` | `MatcherApp.addArg`, `brecOn`, and constructor-equation proofs merged in PRs #245, #246, #248, and #249. PRs #250 and #251 made supported recursion the default and added let-wrapped matches. PR #253 handles distinct parameter-variable indices. Index types depending on other indices and extra dependent parameters now compile with checked constructor equations. A recursive match under an `if` or another match compiles structurally with a checked unfold equation; candidate structural arguments are tried in source order until one compiles. Single-function fixed parameters are inferred from recursive calls and type dependencies. Mutual fixed-parameter permutations, mutual recursion, and general recursive-body equation generation remain open. Computed indices are rejected by Lean structural recursion as well; they are not a required structural parity extension. |
| 11 | Enable matcher compilation by default for ordinary definitions | `Elab/Match.lean`, `Meta/Match`, `Elab/PreDefinition/Eqns.lean` | Merged in PR #244. All CI checks passed; the unchanged Klara specification kernel checks with 69/69 programs. |
| 12 | Retire the direct recursor match compiler | `Elab/PreDefinition/Structural/{FixedParams,BRecOn,Main}.lean`, `Meta/Match` | The removal branch deletes `compile-match-term`, its direct recursor construction, and its structural self-call rewriting. All surface match compilation delegates to Meta.Match. The expression-only API inlines generated matcher values; definition elaboration retains named matchers and metadata. Validate recursive equations, runtime codegen, and Klara before merging. |

Lean's current `Eqns.getEqnsFor?` installs one simple unfold equation for a
nonrecursive definition by default; the matcher's own equations are generated
on demand. The default-on migration follows that inventory instead of retaining
the old per-constructor function equations.

The opt-in Klara run initially stopped at `handleEff-ok`: `simp [handleEff]`
exposed `Option.casesOn`, which `simp` did not reduce. A local fix unfolds
`*.casesOn` definitions; the REPL then reached `smn-step2`.

The generalized recursor now yields constructor-specific equations. Klara's
`smn-step2` proof migration remains in draft PR #1, but the unchanged source
also passes after the no-change `simp` fix; the migration is no longer required
for matcher compilation.

With the opt-in structural matcher switch enabled, a selected 25-test
Nat/List/codegen/inferred-forms corpus improved from 30 failures and 2 errors
to 0 failures and 0 errors after constructor equations and the split-based
proof were added. The nested regression now checks the generated matcher
equations and the single kernel-checked recursive equation. The default-on
audit checks deep runtime recursion using the pre-encoding matcher body,
corresponding to Lean's `_unsafe_rec` runtime source. A temporary Klara copy
with its `lookup-ws` proof reordered to Lean's source-alternative branch order
kernel checked the full specification and ran 69/69 programs. Full Lean parity
still requires computed index expressions and mutual inductives, the full
fixed-parameter analysis, and broader recursive-body shapes before the old
compiler can go.

Do not close a report because a workaround passes: its original reproduction
must pass or fail cleanly as appropriate.

Recent retirement steps: PR #261 added lazy matcher equation hints for grind;
#262 translated legacy explicit IH shorthand before structural elaboration;
#263 moved well-founded recursive matches to Meta.Match and preserved recursive
calls in equation right-hand sides; #265 moved partial definitions to the same
matcher path with atomic rollback. PR #264 fixed the repeatedly observed timing
flake in the discrimination-tree scaling test. PR #266 supplies the expression-only
adapter, including metavariable contexts and hole types in collecting mode.

Lean uses Meta.Match for match expressions and separate structural and well-founded
recursion transformations. Removing the direct match compiler does not imply full
Lean recursion parity: mutual predefinitions/inductives, their parameter permutations,
and broader equation generation still need work.
