# Explicit guest producer build identity

The experimental Java interpreter supports the original Lean.getGithash and
System.Platform.getTarget externs and their original boxed wrappers. Both take
an owned `tagged` Unit and return an object String. This bounded profile requires
canonical Unit zero; invalid direct root input rejects before frames, ownership
or guest effects. Native source ignores its well-typed Unit argument. Strings use
the existing immutable Java String representation, with no guest Node/RC effect.

Build identity is unavailable in every existing Interpreter constructor. A
trusted launch adapter may select `Interpreter.BuildIdentity.supportedLean4331()`
and supply it to the new four-argument constructor `(Program, explicit,
initializing, BuildIdentity)`. The research facade accepts that exact capability
as `:build-identity`; `supported-build-identity` obtains it from the loaded engine
artifact. The fixed supported values are:

- Commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Target: `x86_64-unknown-linux-gnu`.

Those values occur in the accepted producer checkpoint manifest, SHA
`a848092bdd6753f2737a954907747e1bad900c11506ad371fcb8460b576c46d6`, referenced
by accepted producer payload SHA
`486e8c4b486580897f03dd3d46814391e1a5c61044abd4a06f7f4396e806fe9a`.
The manifest records Lean 4.33.1 and 64-bit words. The fixture provenance pins its
four exact original CAS records and the derived fixture bytes; the source receipt
also records matching installed native `--version` and `--githash` observations.
That binary corroboration does not identify the executable that generated the
checkpoint. Pinned platform.cpp returns LEAN_GITHASH, and pinned lean.h returns
LEAN_PLATFORM_TARGET; they do not inspect a JVM or select a target dynamically.

Selecting the profile asserts that the trusted adapter independently accepted
this producer. The constructor does not authenticate a manifest, verify source
hashes, or derive authority from the current checkout, operating system or a
SourceBinding. SourceBinding remains an opaque trusted-adapter identity. The
profile contains no Interpreter, source binding, catalogue, channel or lease;
it has one fixed, immutable supported instance. No arbitrary string profile API
is introduced.

Forks inherit the exact profile. Program installation cannot enable, replace or
remove it. The initialization flag and its one-way completion boundary remain
independent: ordinary and initializing sessions can select the same producer
metadata. Execution without a selected profile rejects; header registration
still describes the original functions without forcing their wrappers.

The focused suite executes both roots/wrappers, default rejection, malformed Unit
preentry checks, guest AP, cached String results, initialization/fork separation,
code-demand fork/installation and Host String replies. No Init image, native IO,
full official frontend completion, automatic producer authentication or general
build-identity compatibility is claimed.

Sources and fixture: [original rows](../test/fixtures/java-build-identity-runtime/README.md),
[pinned platform.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/platform.cpp),
[pinned lean.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h).

The combined isolated jar gate passes 606 test executions / 18,318 assertions
across 69 suites at 384 MiB. Independent source/API review found no blocker.
With an explicitly selected accepted profile, the original header program
completes for `def answer : Nat := 42`: 701 original bodies loaded and 312,634 IR
instructions. Its owned IO success result decodes to `lean-file-header/1`, no
diagnostics, two implicit Init imports, headerEndByte zero, the pinned commit and
the expected 64-bit target. The 43-global companion imports/forks at the same
heap limit. This verifies this header input only; it does not elaborate or execute
the declaration, load a complete project or establish frontend self-hosting.
