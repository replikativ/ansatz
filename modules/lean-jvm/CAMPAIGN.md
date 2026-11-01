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
6. Review documentation against the actual tested implementation before release:
   root and SDK guides, Clojure REPL and Java examples, type/arity and IO support
   tables, producer setup, project/import limits, reload/lifetime behavior, and
   release notes. Run examples from packaged artifacts and audit paths/links.
   Separate released behavior, working prototypes and future work explicitly.
7. Review completeness, compatibility, performance and remaining issues with the
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
- Documentation and launch wording: explain the practical supported profile,
  show core Ansatz and Lean calls together in one REPL, and verify examples
  against the exact package being proposed for release.

## Current follow-up work

### Survey-driven scope proposal

The [reproducible source census](research/type-survey/results.json) covers 3,903
Lean files across nine source strata: pinned Lean Init/Std, compiler/metaprogramming,
compile benchmarks, SciLean library/examples, MCMC executable/formal code, selected
Mathlib data/probability modules, and a TodoMVC application. The
[scanner](research/type-survey/scan.py) reads immutable git blobs and masks comments
and strings. Counts describe lexical definition-header and record-field mentions,
not elaborated signatures, execution coverage, or ecosystem-wide popularity.
[Structured findings](research/type-survey/findings.json) record priorities and
limitations. Corpora pin different Lean versions; their source shapes do not
establish that the current runtime can load those applications.

Concrete observations: Float/Float32 occurs in definition headers in 16 of 37
SciLean example files; Array in 15 of 40 TodoMVC files; Option in 18 of those 40;
Sum/Except in 9 of 68 MCMC executable-directory files. Mathematical real/complex
types also occur in 38 of those 68 MCMC files, including explicitly noncomputable
semantics. Supporting Float or their records cannot make such semantics executable.

Proposed expansion for scope discussion, following the current n-ary/common-value
work:

1. Move Float/Float32 and machine signed/unsigned integers earlier; include Char
   with Unicode-scalar validation. Preserve width, range and floating-point
   semantics explicitly.
2. Add Array and ByteArray as special runtime container families. Their logical
   definitions do not describe their runtime storage; distinguish logical size,
   capacity, copying and ownership.
3. Generalize the constructor codec to closed first-order records, enums, Sum,
   Except and regular recursive datatypes. Use nominal identities, instantiated
   field types and compiler layouts rather than a growing list of special names.
   Reject function/resource fields and unhandled erased invariants explicitly.
4. Add checked adapters for Fin/Vector/Subtype constraints, exact Rat, and selected
   map/set, JSON, URI/path/time interfaces. Prefer actual Lean smart constructors
   and public collection conversions over rebuilding internal representations.
5. Keep function handles, callbacks, Async/Task/IO resources and frontend values
   as separate ownership/capability work. A data codec does not implement a DB
   connection, HTTP stream or filesystem service. Do not promise broad application
   loading solely from the type survey.

The implementation mechanism should remain semantic descriptors plus actual
compiler representation evidence, a small carrier/constructor algebra, and
explicit invariant adapters. These proposals broaden the campaign; they are not
additional released support or a substitute for the release discussion gate.

### Implementation checkpoint

The `feat/lean-jvm-general-call` branch is unlanded. Its native v2 producer
successfully inferred and checked 13 application entries, including multiple
arguments, zero-argument constants, five primitive families, container results and
IO with a nested result. Independent canonical type reconstruction agreed for all
13 entries. A 99-row native-document REPL prototype initialized the real module
world and ran signed integer, Bool, String, Unit and zero-argument value calls.
This prototype bypasses the final source/artifact admission path and is not an
acceptance claim for that public path. Shared admission validation and borrowed container decoding now pass focused
models. Real native-program REPL calls decoded pairs, both Option branches,
Some Unit distinctly from None, lists, and nested IO results, releasing only
the actual owned root. Container inputs and complete public API acceptance
still need integration and review.

The expanded producer was compiled against the pinned Lean checkout and linked
with interpreter symbol export. A second native corpus inferred 12 entries for
machine integers, both float widths, Char, USize, Array, ByteArray, Sum, Except,
and raw nullary scalar results. Independent expected-type reconstruction and
shared row validation agreed for all 12 entries (198 rows). Checked-in actual
metadata fixtures record source/binary/program/request/evidence hashes; they
are not invocation receipts. Signature coverage is not yet codec coverage.

A scalar-free managed constructor recipe API was added to the Java engine.
Its 176 actual-JVM checks cover fresh ownership, explicit release, bounds,
invalid references/aliases, caller-array isolation and refused lifecycle states.
The host-only argument planner passes 11 tests / 40 assertions, including
nested options, proper lists, copied sharing, cycle refusal and layout field
order. Its runtime materializer and construction/start ownership journal must
still be integrated before container input support is advertised. Focused models
currently pass: signatures 4/67, entry observations 6/36, expanded entry
observations 7/73, borrowed values 14/54, package audit 5/23 (tests/assertions).
The built SDK JAR, including the argument planner, passes 103 tests / 536 assertions. The separate Java
application-JAR consumer also passes typed and general calls, generic arity/type
rejection without poisoning the Project, Clojure wrapper calls, generic IO Unit,
thread handoff and close checks using a genuine historical artifact. This is
v1 artifact compatibility plus the general facade; the v2 public source/cache/
artifact round trip and actual container input calls remain pending. The published `0.2.578` boundary remains the three
original profiles.

Documentation review should also reconcile historical Init-tier/count examples
with the actual proposed package. In the retained combined REPL, published core
`0.2.578` loaded 5,118 declarations in its reported medium tier and ran the DSL
alongside the optional interpreter. Preserve historical receipts as historical;
verify current examples instead of copying their older counts into launch claims.
