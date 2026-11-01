# Borrowed Name equality

Implemented research profile, 2026-10-30. The original `Lean.Name.beq` extern
uses the exact ABI `[tobject,tobject]`, both borrowed, returning uint8. Its pinned
`lean_name_eq` algorithm comes from Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, runtime/object.cpp:2769–2800.

The primitive creates no guest object, owner credit or identity stamp. It checks
the initial cached UInt64 hashes, then walks parent heads iteratively. It compares
constructor tags and exact String or full Nat components, returning early for
shared parents. Parent hashes are not rechecked; upstream deliberately comments
that repeated test out. Hash equality alone is insufficient, including genuine
large numeric components whose Name hash uses the fallback value 17.

Raw owned root entry, PAP, makeClosure, prepared-graph closure import, defensive
AP and first-class closure admission require an owning guest wrapper. Host replies
cannot introduce a raw borrowed-native closure. The genuine `._boxed` wrapper
calls the primitive, decrements its second and first owned arguments in that
order, then boxes the Boolean. Static typed FAP preserves the borrowed ABI.
No automatic borrowed facade adapter or rewritten original body is introduced.

## Representation and trust boundary

Only Long zero denotes anonymous Name, regardless of Java Long object identity.
A current heap head must be a live constructor Node with tag 1 or 2, two object
fields, eight scalar bytes and no closure payload. Array, ByteArray, ref and
ready-task kinds reject. Existing pointer-owner checks reject foreign stamped
Nodes before the alias shortcut. String heads require String leaves; numeric
heads require nonnegative Long/BigInteger leaves, compared by magnitude.

These are **shallow current-head guards**, not proof that an arbitrary graph is
a well-typed Name. Valid Unicode Strings, correct cached hashes and well-founded
Name prefixes remain trusted value invariants supplied by genuine constructors
or an independently accepted source adapter. General prepared-graph admission
alone does not establish them. An alias shortcut does not audit the whole parent
chain, and an initial hash mismatch does not visit its tail, matching the native
valid-value fast paths. Valid Unicode Java String equality agrees with exact UTF8
bytes without normalization; corrupt native byte buffers are outside this model.

The parent walk uses constant auxiliary storage, without Java recursion or a
visited-pair set. It has a one-million-head step ceiling. An unresolved traversal
past that ceiling raises a named depth/cycle profile error, rather than silently
returning equality or hanging. This is not a general cycle validator: aliased
cyclic heads may take the native alias shortcut, and cyclic graphs remain outside
the trusted well-founded Name domain. No source hash, component or prefix is
repaired or recomputed to conceal invalid metadata.

## Bounded evidence

The two original rows and genuine wrapper are pinned in
`test/fixtures/java-name-equality-runtime/`: SHA256
`49721fcc78723aeec0798bedcd270bbb73fbc555e0adf3ed75ca86ddcf0adb94`.
Only optional pretty text was removed. Tests construct Names through the existing
genuine constructor/hash fixture, including embedded NUL and supplementary
characters, large Nat collisions, mixed tags and shared prefixes. Deliberate hash
corruption probes verify the exact top-hash-only algorithm; they are not genuine
source-state credentials.

Eleven focused tests / 84 assertions pass in both drivers, with explicit-only host reply cases.
They cover wrapper owner release, raw/closure guards, pointer-metadata forks,
foreign admission, 12,000-component chains, malformed current heads/leaves and
bounded nonterminating nonalias cycles. Failures assert no primitive RC/store
effects; no arbitrary failed-frame cleanup is claimed.

The original Trie insertion path also exercises IR `del` on immediate zero.
Pinned `lean.h` lean_del_object ignores tagged immediates. Both drivers now use
one shell-deletion helper that preserves this rule. Heap deletion retains the
existing unique-shell check, clears moved fields without decrementing their
transferred credits, and records one shell deletion. Regression tests cover
immediates and the retained child credit after deleting a unique parent shell.

The combined isolated jar gate passes 590 executions / 18,193 assertions across
67 suites at 384 MiB. The source-derived 43-global companion imports/forks in the
retained REPL. Original header execution then reaches 625 loaded bodies / 294,183
instructions and stops at unsupported Lean.getGithash. No full Init/frontend
image was restored, and this is not complete frontend/file execution or a public
bundle claim. Build identity needs its own accepted producer/runtime profile.
