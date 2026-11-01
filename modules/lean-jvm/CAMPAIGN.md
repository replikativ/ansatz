# Lean/JVM integration campaign

## Release coordination

The user requested discussion of the broader interop design and other open issues
before the next release. Development and review can continue locally. Do not merge
this campaign's follow-up branches to main or publish another version until that
discussion has happened and the user has agreed to the release scope. Main currently
automatically deploys both core Ansatz and the optional SDK.

## Established baseline

`org.replikativ/ansatz` and `org.replikativ/ansatz-lean-jvm` version `0.2.578` are
published. PRs #367 and #368 landed the bounded source pipeline and optional SDK.
The SDK resolved through ordinary Maven and passed the actual Java application-JAR
consumer. The separate pinned Linux native producer bundle is published in
ansatz-stores; see [producer setup](producer/README.md).

Core Ansatz remains the kernel, Clojure elaboration DSL and store services. The
optional SDK executes Lean compiler IR and uses the official native frontend for
source compilation. Executing an exported Lean function does not import its
declaration or theorem into the core DSL/kernel environment.

The published external call boundary supports only Nat-to-Nat, String-to-String
and IO Unit, selected through explicit checked entry requests. Internal execution
supports broader arities and values. The source profile covers Init plus a closed
local module DAG, not general Lake, Std, Lean or Mathlib project imports.

## Next practical interop slice

1. Agree the signature/codec contract before expanding the implementation.
   Use one named function handle and general argument-list invocation for Java
   and Clojure. Preserve the existing typed Java helpers as conveniences.
2. Generalize native checked export evidence. Discover requested functions'
   actual parameter and result types, binder information, and runtime calling
   conventions. Remove the three-signature whitelist rather than infer types
   from erased IR. Capture transitive dependencies and initialization normally.
3. Support variable arity and closed monomorphic signatures over Nat, Int, Bool,
   String and Unit. Add recursive products, Option and List over supported types
   as the proposed first useful application slice. Decide whether Float belongs
   in this slice. Arrays and ordinary records follow through the same type/layout
   machinery. Unsupported types or specializations produce explicit errors.
4. Implement type-directed argument/result conversion and exact callable dispatch.
   Keep argument refusal before guest effects, result ownership/retirement intact,
   named IO dispatch exact, and unsupported runtime capabilities explicit. Extend
   to IO results whose value type has an admitted codec; runtime IO operation
   coverage remains a separate constraint.
5. Validate from a retained REPL with core Ansatz and the SDK together: ordinary
   Clojure function calls, DSL usage alongside them, editing/reloading Lean source,
   multi-argument Bool/product/container examples, and precise unsupported cases.
   Check actual native Lean behavior and packaged Java consumers as separate gates.
6. Review completeness, compatibility, performance and remaining issues with the
   user. Agree the next release scope before merging or publishing. Passing tests
   alone does not satisfy this release coordination gate.

## Decisions to discuss before release

- Host representations for products, records, Unit and Option. Preserve
  `none` versus `some ()`; avoid accidental ambiguity or lossy numeric conversion.
- Entry selection for REPL and deployment: explicit roots, signature discovery,
  module-wide exports, and possible lazy admission. Existing requested-entry
  inventory is not a complete index of all declarations in an imported module.
- Specialization of polymorphic/implicit/dependent parameters and erased proofs.
  Closed monomorphic support is the proposed initial boundary.
- REPL reload semantics: replacing code versions, rebinding handles, preserving
  or recreating initialized state, and invalidation/close behavior.
- IO results, actual supported IO operations, error/output handling and Lean-to-JVM
  callbacks. Bidirectional interop needs its own explicit effect/lifetime contract.
- Kernel/DSL integration: sharing declarations and applying imported theorems is
  distinct from runtime invocation. Retain the original goal and define the trust
  and store/provenance boundaries before presenting it as supported.
- Supported project/import corpus and the next steps toward Std/Lean/Mathlib and
  eventually hosting the frontend. Keep self-hosting claims separate from native
  frontend-assisted source loading.
- Resource and performance limits on representative application programs,
  including allocation, marshalling, instruction/time budgets and numeric/string
  bounds. Keep the REPL loop tight; avoid giant image experiments by default.
- Forking and persistent state alignment with Klara, plus later AOT/JIT hooks.
  These remain campaign goals; the first public API does not expose forks.
- Public Clojure ergonomics, Java API shape, artifact separation, producer updates
  and release gating. Factoring out the Clojure elaborator can be considered
  independently of runtime execution support.

## Current follow-up work

The `feat/lean-jvm-general-call` working branch contains an unlanded prototype of
the general Java function handle and public Clojure wrapper. It still uses the
three existing checked profiles. REPL probes established general-call syntax,
exact integer conversion, named IO calls and argument-refusal behavior; they do
not establish the broader type/arity slice above. Complete exporter and codec
work, review, and acceptance remain necessary before making those claims.
