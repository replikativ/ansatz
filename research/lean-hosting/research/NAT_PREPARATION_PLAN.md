# Object-family and RC preparation before Nat compilation

Status: first data-only Nat preparation increment. Execution remains the existing
reference/mutable/JVM interpretation. Small-Nat representation, arithmetic and
promotion fallback are a separate following increment.

Extend `typed-blocks/prepare-unit` without changing its call signature or ordinary
lowering. Preserve the existing schema's canonical-register blocks, origins,
scopes, resource limits and exact `legacy-body` reconstruction:

- Admit nonnegative numeric literals with IR type `object`, `tagged` or `tobject`.
  Retain the exact declared type and literal carrier/value. Do not infer a Nat
  parameter domain or claim that an `object` is an immediate. These are
  producer-declared structural facts, not an independent proof of native pointer
  layout: even a deliberately oversized literal annotated `tagged` is retained as
  data, without granting a small-immediate or nonreference optimization proof.
  Future Nat lowering must range-check literal values as well as entry operands. Existing unboxed
  scalar literals keep their width/range validation; `void` is excluded.
- Admit canonical `:inc` and `:dec` instructions. Their block has one RC operation
  and an identity-register `:next` transfer. Preserve local ID/type, count,
  producer `:check` and `:persistent` annotations, one canonical PC and one origin.
  RC does not bind a new variable. Validate paired body/companion count, local and
  persistent shape; the producer check bit is retained provenance because ordinary
  lowering intentionally omits that flag from its executable instruction.
- Type compatibility is directional: exact equality plus `tagged -> tobject` and
  `object -> tobject`. It is not object-family equality. Never admit the converse,
  `object <-> tagged` or `void` through this extension. Borrow annotations remain
  separate signature facts and are not changed by compatibility.
- Unsupported operations still fall back, malformed admitted facts still reject.
  No heap, counter, ownership, MPZ allocation, interop or executor semantics change.
- Existing M3b selection explicitly declines new object literal/RC shapes before
  calling Pattern. The scalar represented grammar and emitter do not accept Nat
  as an accidental consequence of this preparation extension.

Pinned upstream evidence is Lean
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:
`src/Lean/Compiler/IR/Basic.lean` distinguishes definite-reference `object`,
immediate `tagged` and union `tobject`; its `isObj` also includes `void`, which is
not a Nat proof. `Checker.lean` checks full-call arity/operand scope, not exact
argument type equality, and RC instructions only require a known local. The
stronger directional compatibility above is a conservative supported preparation
policy, not an assertion that other upstream programs are malformed.

Tests must retain actual existing producer rows (including borrowing) rather than
inventing an owned Nat.add ABI. Use bounded fixture selection, paired lowering,
independent block assertions, exact canonical roundtrip and every small-fuel
reference/mutable/JVM snapshots for RC on ordinary integers and existing local or
imported MPZ refs. Such refs are runtime inputs, not new arithmetic producers.
Include persistent annotations, malformed facts/locals and resource limits. No
native export, full Init restore or Source catalogue is needed for this slice.

The first REPL run will load only these small preparation namespaces/tests in one
bounded resident JVM, shared serially with the session integration work. This
increment does not establish compiled Nat execution or native MPZ allocation and
heartbeat parity.
