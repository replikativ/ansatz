# Polynomial reflection

`ring` uses the identity-normalization path from the pinned Lean 4.33.1 grind
ring implementation. It reifies both sides of an equality into
`Lean.Grind.CommRing.Expr`, shares an atom table across both sides, and constructs
the balanced absolute-pivot `Lean.RArray` context used by Lean.

For commutative semirings, including `Nat`, the proof applies
`Lean.Grind.CommRing.eq_normS`. For commutative rings, including `Int`, it applies
`Lean.Grind.CommRing.Expr.eq_of_toPoly_eq`. These are upstream proved theorems,
included with their dependencies in the reproducibly generated bundle. They are
checked during bundle validation; they are not introduced as axioms.

The tactic supplies a reflexivity proof of `Bool.true` for the normalization
certificate. Strict kernel checking must reduce the certificate computation to
`true` and verify that its denotations match the original goal. The goal is
assigned only after that check. There is no trusted Clojure polynomial equality
test or native boolean oracle in this proof path.

Operations are recognized only when definitionally equal to the operations of
the selected `Lean.Grind.CommRing` or `Lean.Grind.CommSemiring` instance. Local
instances and higher type universes are supported. Unsupported subexpressions
remain atoms: in particular, truncated `Nat.sub` is never interpreted as ring
subtraction, and powers with a nonconstant exponent remain atoms. Numerals,
addition, multiplication, natural powers, and ring subtraction/negation are
represented by the corresponding upstream expression constructors.

Relevant Lean sources are
`Lean/Meta/Tactic/Grind/Arith/CommRing/{Reify,Functions,Proof}.lean`,
`Lean/Data/RArray.lean`, and
`Init/Grind/Ring/{CommSolver,CommSemiringAdapter}.lean`.

This ports polynomial identity certificates. Integration of equality hypotheses
into grind's polynomial constraint solver, characteristic-specific reduction,
noncommutative solving, and ordered-ring reasoning are separate work. Surface
arithmetic selects local generic carriers and propagates them into numeral
subtrees before instance synthesis, following Lean's `binop%` elaboration.

The executable regression corpus is `test/ansatz/tactic/ring_test.clj`, with
native Lean reference examples in `test/lean/ring_reflection.lean`.
