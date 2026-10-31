# Checked source declaration fixtures

These exact prelude-only inputs were processed by the original Lean4.33.1
frontend IR hosted in the Java runtime, under the strict finite Java kernel
declaration adapter. Theorems.lean reaches EOF with two axioms and two theorem
publications. Noncomputable.lean reaches EOF with one axiom and two safe
definition publications. Both cases preserve historical checked versions,
observe no command errors, and complete owner/session/runtime cleanup.

The explicit axioms keep these examples independent of logical Init imports.
They are assumptions, not newly proved facts. Noncomputable suppresses executable
compilation; these results do not establish generated-code execution, general
imports, library-project support or the public loader facade. Runtime source
companions, source provenance and the finite checking adapter are required.
The large original frontend fixture is separate from the ordinary CI test basis.

The pinned upstream source object is
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. See the experimental
[frontend campaign](../../../research/LEAN_HOSTING_CAMPAIGN.md) and
[full Expr runtime](../../../research/JAVA_EXPR_FULL_RUNTIME.md).
