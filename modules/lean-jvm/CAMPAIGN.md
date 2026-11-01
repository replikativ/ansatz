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

The unmerged `feat/lean-jvm-general-call` branch implements the general Java and
Clojure function boundary, managed constructor/scalar/array/byte arguments,
borrowed result decoding, exact ABI/evidence validation and bounded recursive
carriers. The native producer uses actual LCNF representations and constructor
layouts. Raw result decoding follows the Java engine's external carrier contract,
rather than confusing those values with raw IR bit words or boxed guest nodes.

The genuine two-file, 16-entry common corpus and 16-entry scalar/buffer/choice
corpus run through source compilation, artifact export/loading and public Java
and Clojure APIs. Container identity, projection, discarded inputs, both option
branches (including Some Unit), nested IO results, array/byte updates and all
machine integer widths have actual execution coverage. Official Lean `--run`
agrees on the representative scalar/array/bytes/choice oracle. The implementation
adds only nine exact audited numeric externs needed by the tested closures;
data codec support is not general IO or application compatibility.

The diagnostics-aware typed producer keeps warnings/info on stderr and structural
JSON on stdout. Process monitoring, cache validation and artifact provenance
retain the actual bounded diagnostic bytes and independently pinned producer
pairs. Errors still fail; no diagnostic suppression or guessed JSON recovery is
used. Both legacy and v2 producer cohorts remain explicit.

The source acceptance gate passes 35 checks at a 512 MiB JVM heap: cold/cache
loads, source edits, old-handle stability, artifact reload, warnings (including
cache and artifact), frontend errors, unclassified capabilities, higher-order
entry refusal and nullary Float32/64/high-bit machine results. Observed cold
common load was about 6.8 seconds, cached source load 4.0 seconds, and artifact load
132 ms in the final candidate run. These are probe timings, not cross-platform benchmarks or
performance guarantees. Hashing already streams with a 64 KiB buffer; no whole
producer executable is read into a JVM byte array for pin checks.

The final required packaged-JAR, application-consumer and ownership/resource
check sequence is recorded in [release-candidate.json](release-candidate.json).
Read [RELEASE_REVIEW.md](RELEASE_REVIEW.md) for tested scope, remaining limitations
and the user-controlled publication/landing sequence. The v2 native archive is
prepared locally and has not been published. Main and published Maven artifacts
remain unchanged.

The broader type survey's records, regular recursive ADTs, constrained adapters,
callbacks, public forks and frontend-hosting work remain follow-up work. The
published `0.2.578` boundary remains its original three profiles until landing.

Historical Init-tier/count examples should be checked before launch claims. A
retained combined REPL previously loaded 5,118 declarations in core `0.2.578`'s
reported medium tier and ran the DSL alongside the optional interpreter; this
campaign does not change core stores or kernel checking.

### Consolidated implementation

Production Java now lives under `modules/lean-jvm/src-java/ansatz/lean/jvm/`;
the canonical engine and package-private stateless helpers use
`internal.exec`. An explicit three-source engine closure and compiled-class
inventory replace the old single external-source packaging assumption.
The [architecture guide](ARCHITECTURE.md) documents ownership boundaries.

The tracked `experiments/lean-ir` tree is removed. Maintained frontend work,
comparison oracles and the unpublished legacy facade have moved to
`research/lean-hosting`; 19 closed probe implementations were retired. Original
capture bytes and source-at-commit references remain intact. The production CI
lane checks the canonical Java engine; legacy World/facade/Pattern checks have
an explicit optional research lane. Both paths retain their distinct contracts.

Fresh consolidated gates pass 124 SDK tests / 733 assertions, 163 engine groups
(1,553 tests / 60,565 assertions), all application consumers, native source
acceptance, ownership/resource tests and stateless helper checks. See the current
candidate receipt for exact hashes, source cohorts and optional research results.
The native producer binaries and their independently admitted source bytes are
unchanged by relocation. No merge or publication has occurred.

The complete optional research lane also passes after using a workspace-local
Git dependency cache: its legacy facade/World/controller/RAW/coherent checks and
94 Pattern/compiler tests remain available without gating the public SDK release.
The current receipt records their separate scope. The consolidated retained REPL
also loaded a genuine artifact and exercised common calls without JVM restarts.

## Agreed prelanding follow-up (2026-11-01)

The user authorized these four implementation/review items, while retaining the
release discussion gate:

1. Provide supported Java and Clojure build-time artifact preparation and a CLI.
   Preparation uses the checked native compiler/evidence pipeline and exports its
   receipt; it does not open a JVM Project or invoke guest startup or main. Native
   frontend metaprograms can still execute during trusted source compilation.
2. Replace the incidental 16-selected-function limit with an explicit resource
   bound of 1,024. Keep independent request-byte, IR/dependency, artifact-size,
   execution and arity limits. Older native producer cohorts retain their own
   preparation limit; existing artifacts and admitted producer pairs stay valid.
3. Keep ordinary Clojure values and simple JVM carriers. Preserve the distinctions
   between None and Some Unit, between Sum branches, exact integer ranges and
   float widths. Test recursively mixed Clojure and Java carriers.
4. Review the build/deploy examples and compatibility scope, regenerate the exact
   unpublished producer candidate, and prepare the publication/merge sequence.
   Approval to implement these items does not authorize publication or merging.

A genuine project with more than 16 selected functions must pass preparation,
artifact loading and calls against the built SDK JAR. Keep this separate from
builder boundary tests and from claims that every 1,024-entry project fits the
other resource budgets.
