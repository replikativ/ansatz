# Original kernel projection layout evidence

Five authentic rows preserve typed Names, original raw CAS hashes and bodies;
only top-level `pretty` is removed. The declarations are Name.str._override,
Level.succ._override, Expr.sort._override, mkAxiomValEx and the actual
elabAxiom._lam_3 that constructs Declaration.axiomDecl. Their constructor
metadata establishes the six physical tag/field/scalar layouts used by tests.

The checking tests construct model descriptors in those source layouts and
import them as real Java interpreter Nodes. They do not claim execution of the
original frontend or correspondence of intentionally ignored computed caches.
The adapter reuses existing semantic projection and constructor storage rules.

`provenance.json` pins bytes, Lean source and Apache 2.0 LICENSE at Lean 4.33.1
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, from source index
`74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.
Upstream rows/source are copyright Microsoft Corporation and Lean contributors.
See [the carrier projection report](../../../research/JAVA_KERNEL_CARRIER_PROJECTION.md).
