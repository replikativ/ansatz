# Typed JVM host bindings

Status: candidate source/artifact admission, registry and runtime adapter are
implemented. The v4 producer has been built and exercised locally; publication,
and release remain pending. Local exact-JAR, engine and native-reference
acceptance passed; hosted CI remains a release gate. See the [API guide](FFI.md).

## Contract

Lean owns the logical signature and an executable reference definition. The host
supplies an implementation and an explicit implementation label. A generated,
authenticated manifest joins the structured declaration Name, defining product,
logical types, runtime argument mapping, effect, original Header and lowered ABI.
The registry does not repeat types or grant authority to caller-authored schemas.

The first public profile will support synchronous, first-order pure functions
using the existing v3 value types. Purity and equivalence are host obligations;
neither Java typing nor a version string proves them. Unexpected exceptions stop
the invocation; expected failures use Except. No host implementation supplies
proofs or adds kernel axioms. Native-style proof evaluation using foreign
implementations requires a separate explicit trust policy.

Capture the Clojure IFn value once per Project generation. This prevents direct
Var rebinding from changing that target, but does not freeze transitive Vars,
dynamic bindings, mutable captures, or external state. A changed implementation
opens a new Project generation. No automatic retries are performed. Existing Lean
closed-value caching remains part of execution; callback counts are not promised.

## Execution and ownership

1. Match the actual pending request and its registered descriptor by identity.
2. Export arguments using admitted LeanTypes and actual ABI lanes. This validates
   and freezes pure storage before user code sees detached immutable values.
3. Invoke user code without exposing Nodes, requests, engines or owner tokens.
4. Prepare the result against the admitted result type. Scalar replies retain
   their exact lane and bit pattern; object replies use certified frozen storage.
5. Resume only after every object input is certified frozen. Its old owning
   occurrences then have the existing persistent rc0 semantics; borrowed inputs
   are never decremented. Returning an input therefore requires no guessed INC.
6. Fail the actual pending request on callback/conversion failure. Preserve fatal
   failures and cancellation; do not manufacture a Lean result or replay work.

The engine completion seam is task-free and accepts only an unforgeable private
prepared-reply token. It does not admit signatures, source, or host code. Existing
generic resumeHost and ownership contracts remain unchanged.
The only admitted enclosing native action is the exact current String.any
predicate continuation (including nested workers); other task/resource/release
protocols are refused. Failure retirement recognizes only the actual runtime
owner/current Program Function and its exact selected descriptor, with one
pending or failed packet and no parent completion. The prior stopped-heap and
filesystem resource-ledger checks still apply.

## Compiler integration gate

A function-name replacement after compilation is insufficient: inlining,
specialization, constant evaluation and compiler simplification may remove calls.
Likewise the current interpreter selects all/c externs, not jvm externs.

The candidate uses standard noinline definitions instead of introducing new Lean
syntax. The independent v4 producer observes the noinline attribute and pure
definition eligibility beside existing nominal signature/layout evidence.
Only those selected original Headers can receive per-Project implementations.
Original IR is unchanged, and registration precedes all body materialization and
guest initialization. The selected registry supplies no second type signature.
No v3 producer or archived evidence is retrospectively assigned new authority.

A small Lean 4.33.1 IR probe confirmed that noinline retains a direct function
call while a call with constant arguments can move into a closed declaration.
Consequently, admission must cover those original declarations too. Installing
bindings only after initialization can miss early calls, and callback counts
are not part of the pure-function contract.
Purity permits hoisting/caching, but the chosen implementation must remain stable
for the entire Project generation. This observation does not establish a full
optimizer-preservation contract for an import annotation.

## Sequence and acceptance

1. Implemented private typed adapter: identity and modified returns, zero/multiple arguments,
   borrowed/repeated inputs, scalar lanes, aliasing, malformed results, cancellation,
   stale/foreign requests and fatal errors. Use synthetic IR only as engine tests.
2. Implemented v4 producer/admission: exact definitions and generated signatures, missing/extra and
   duplicate bindings, nominal same-lane mismatches, stale products, effects,
   finite monomorphic instances and optimizer-preserved boundaries.
3. Implemented Java/Clojure registry and portable two-file example. Factories
   derive nominal constructors once from detached signatures. The native
   reference oracle uses the Lean implementation rather than a foreign callback.
4. IO bindings and exception envelopes/capability lifetimes. Reentrancy, function
   callbacks, resources, async execution and fork/replay policies follow later.

Host work is cooperative: guest instruction budgets do not preempt arbitrary
in-process Java/Clojure. Forks and computational proof admission are not enabled
by this slice. Existing filesystem restrictions continue to apply.

## References

- Lean source: src/Lean/Compiler/ExternAttr.lean,
  src/Lean/Compiler/ImplementedByAttr.lean, src/Lean/Compiler/IR/ElimDeadVars.lean,
  src/Lean/Compiler/IR/EmitC.lean and src/include/lean/lean.h.
- [Lean replacement and proof-trust semantics](https://lean-lang.org/doc/api/Lean/Compiler/ImplementedByAttr.html)
- [Lean FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/)
- [Clojure Vars](https://clojure.org/reference/vars) and
  [direct linking](https://clojure.org/reference/compilation)
- [JVM MethodHandle](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/invoke/MethodHandle.html)
