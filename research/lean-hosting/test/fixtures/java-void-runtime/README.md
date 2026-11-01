# Original Void runtime evidence

Pinned Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).
Accepted original IR index: `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.

`original-rows.json` contains exactly `Void.mk` and its genuine `Void.mk._boxed`
wrapper. Raw CAS bytes were checked against the stored SHA-256 and exact typed
Name from the index-derived disk catalogue. Only optional top-level `pretty` was
removed; each row SHA still identifies complete original CAS bytes. Source and
normalized fixture hashes are in `provenance.json`. There are no initialized
dependencies in this two-row closure. Upstream code is Apache-2.0; see `LICENSE`.

`Init/System/ST.lean:22` gives the opaque extern. `include/lean/lean.h:3029` drops
its owned payload with `lean_dec` and returns `lean_box(0)`. The erased IR argument
is omitted from the actual C parameter list. The original raw ABI is
`(erased owned, tobject owned) -> void`; the genuine wrapper has two owned
`tobject` arguments and result `tagged`. The engine's existing object lane
carries both void and tagged zero; no new scalar lane or guest world object is
introduced.

The focused suite executes these original rows alongside explicit IR and private
ownership-boundary models. Deferred Promise/finalizer checks use the existing
original task fixture, not replacement guest implementations. No separate native
Void oracle was run; pinned native source and authentic IR provide the semantic
evidence. The fixture does not admit adjacent native world operations or claim
that an arbitrary erased/world token has been authenticated.
