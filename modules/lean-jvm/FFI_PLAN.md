# Typed JVM host bindings

Status: implementation in progress. No public source/artifact binding API is
admitted yet. The first slice is the private typed suspended-call adapter.

## Contract

Lean owns the logical signature and an executable reference definition. The host
supplies an implementation and an explicit implementation version. A generated,
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
opens a new Project generation. No automatic retries or memoization of host calls.

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

## Compiler integration gate

A function-name replacement after compilation is insufficient: inlining,
specialization, constant evaluation and compiler simplification may remove calls.
Likewise the current interpreter selects all/c externs, not jvm externs.

Before public registration, add a producer-owned JVM import annotation or wrapper
mechanism which retains the Lean body for reference/native execution and emits
an explicit JVM host-call boundary. Authenticate that association together with
v3 logical/layout evidence. Neither an unchecked symbol map nor hand-edited IR
is a substitute. Account for nullary calls and optimizer purity assumptions.
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

1. Private typed adapter: identity and modified returns, zero/multiple arguments,
   borrowed/repeated inputs, scalar lanes, aliasing, malformed results, cancellation,
   stale/foreign requests and fatal errors. Use synthetic IR only as engine tests.
2. Producer/admission: exact imports and generated signatures, missing/extra and
   duplicate bindings, nominal same-lane mismatches, stale products, effects,
   finite monomorphic instances and optimizer-preserved boundaries.
3. Public Java/Clojure registry and portable example; native reference oracle
   must use the Lean implementation rather than the same foreign callback.
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
