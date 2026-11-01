# General Lean/JVM interop release review

This is an unmerged release candidate. No SDK or native producer publication is
authorized until the user reviews scope, documentation and the landing sequence.
Published `0.2.578` retains its original three checked entry profiles.

## Proposed scope

One general named function handle, zero to 64 explicit arguments, pure and IO
results, and the closed types in [the carrier table](README.md#values-resources-and-lifetime).
The practical corpus consists of original Ansatz two-file common-value programs
and a scalar/buffer/choice program, plus the unchanged external FP Lean tutorial
already covered by the preceding release. Portable fixtures carry actual native
source/build evidence and run through the same public Java and Clojure APIs.

The SDK remains optional, separate from core Ansatz. Existing core kernel,
Clojure elaboration DSL and store loading are unchanged. Core and SDK can share
a Clojure REPL; runtime invocation does not import kernel declarations or proofs.
No LLVM or Pattern dependency is introduced.

## Required acceptance

- Exact SDK source inventory and Java source pins; JDK 17 build and ordinary Maven
  dependencies, without the source checkout on consumer classpaths.
- Packaged-JAR models, actual construction/release/limit checks, legacy consumer,
  both general consumers and archive tampering negatives.
- Public source cold load and cache hit, edits creating a new Project while old
  handles retain old behavior, exported artifact reload, warnings on stderr,
  frontend errors, unsupported capabilities and unsupported entry types.
- Native Lean comparison and actual execution of scalar arithmetic, wrapping,
  raw nullary results, both float widths, arrays, bytes, Sum/Except and IO results.
- Documentation examples, relative links, producer hashes and attribution audited.
- Final read-only correctness and completeness review; findings resolved or
  disclosed. Validation counts and candidate byte hashes belong in
  [the candidate receipt](release-candidate.json), not historical receipts.

## Limitations to keep visible

- Trusted source only; official native Lean frontend required to compile source.
  No frontend self-hosting, automatic toolchain install or general Lake support.
- Init and a bounded local acyclic import graph. Installed Std/Lean/Mathlib imports,
  modern `module` headers and external package resolution remain outside scope.
- Explicit selection of at most 16 entries per project. No module-wide export,
  implicit specialization, polymorphic/dependent/higher-order entry arguments,
  arbitrary records or recursive ADTs, or erased-proof construction.
- IO data conversion is broader than IO service coverage. Captured output and a
  finite audited intrinsic set do not provide arbitrary filesystem/network/task
  capabilities or Lean-to-JVM callbacks.
- Public forks, cross-project guest handles, hot code replacement and initialized
  state migration remain future work. Reload creates a new Project version.
- Interop limits and cooperative execution budgets are explicit. This campaign
  does not claim performance parity with compiled Lean or general application
  compatibility from the type survey.
- Validation is on Linux x86-64/JDK 17-compatible bytecode. Other JVM platforms
  have not been acceptance-tested here.

## Landing discussion

1. Agree the carrier conventions (notably Unit, Option, Sum/Except, code-point Char
   and float widths), explicit entry inventory and unsupported-type errors.
2. Confirm the bounded corpus/import/IO scope is appropriate for the next release.
   Arbitrary records, constrained Fin/Vector/Subtype/Rat adapters, callbacks and
   the original frontend-hosting agenda remain documented follow-up work.
3. Approve publication of the prepared v2 producer bundle and its exact inventory
   to ansatz-stores. It is needed for discovered signatures and clean frontend
   diagnostics; the published v1 bundle remains available for legacy consumers.
4. Publish and verify that exact bundle first, update its download instructions,
   then merge the SDK follow-up. Main automatically builds, tests and publishes
   coordinated core and optional SDK releases; merging is itself a release step.
5. Use the release's actual coordinated Maven version, not the historical
   `0.2.578` version or a candidate test JAR. Retain exact CI JAR/POM receipts.

This sequence is prepared for review. Passing checks does not authorize steps 3–5.
