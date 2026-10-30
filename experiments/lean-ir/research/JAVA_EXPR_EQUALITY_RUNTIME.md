# Borrowed Expr equality in the Java research interpreter

The Java engine implements the exact borrowed two-object/UInt8 ABIs of
`lean_expr_eqv` and `lean_expr_equal`. Owned access uses the authentic boxed
wrappers. Both preserve cached data rather than computing/replacing it.

The source algorithm is pinned `kernel/expr_eq_fn.cpp`. Expr identity precedes
low32 cached-hash and tag checks. Both modes compare expression structure,
ordered metadata entries, projection names/indices and let nondependency.
`equal` additionally compares lambda/forall names, binder annotations and let
names; `eqv` omits those annotations. Intermediate application function spines
omit hash tests exactly as the native algorithm does. Full cached-word equality
would be incorrect. Level comparison is structural (kind, low32 hash, depth for
succ/max/imax, ordered children), not universe equivalence; cached flags are not
compared independently.

Metadata compares the list of Name/DataValue pairs in order, preserving duplicates.
All six DataValue kinds are handled, including signed Int and Syntax. Syntax
comparison ignores SourceInfo but compares node kinds and logical array elements,
atom text, and identifier repaired raw substrings, Names and ordered preresolution
entries. Substrings use the existing read-only repair view; the owned substring
intrinsic is not called. Native-aligned scalar storage is accepted where needed:
Expr binder/let semantic9 or padded16 bytes; metadata Bool semantic1 or padded8.
Padding and source caches are read without rewriting them.

A synchronous invocation-local typed work stack and active/completed identity-pair
memo avoid Java recursion and repeated completed DAG work. Scratch does not escape
into Program/Node state or failure diagnostics. No guest credits, fields, flags,
cache words or engine ownership counters are changed by comparison. Ordinary
constructor checks are structural storage checks; they do not establish nominal
Expr/Level/Syntax identity or recursively certify every reachable object.
Identity shortcuts and early false results also do not certify an entire graph.

The explicit host profile rejects encountered nontrivial comparison cycles,
more than1,000,000 charged work units,100,000 typed pairs or100,000 pending work
frames. Charges include cumulative Name prefix steps, String UTF16 lengths,
Substring source lengths and BigInteger words; interrupt checks occur when work
crosses a1024-unit bucket. Limits are bounded host guards, not native heartbeat
counts or native timeout parity. A single primitive is synchronous and not a
fork/suspension boundary; its scratch is discarded before the next VM boundary.
The current allocation-only lab heartbeat adapter remains a distinct experiment.

Raw borrowed native root entries, PAPs, closure factories, prepared closure
imports and first-class/host-returned raw closures are rejected before ownership
claim, following the existing Name/Expr-data fences. Direct typed FAP from an
owned guest wrapper remains supported. There is no native Meta replacement,
projection through Java kernel classes, AST storage representation change, new
Node field or importer expansion.

Validation evidence is in `test/fixtures/java-expr-equality-runtime`; focused
checks are `research/java-ir-baseline/expr-equality-checks.clj`. Native reference
outputs are independent of the model adversary tests. First-axiom admission and
completed frontend elaboration are not established by this runtime family.

The original Expr constructors also require the exact scalar casts
`UInt8.toUInt32` and `UInt64.toUInt8`. Their raw ABIs have one nonborrowed input
(U8→U32 and U64→U8). The implementation preserves the byte value when widening
and masks the low8 bits when narrowing, after existing external lane validation.
The authentic boxed wrappers perform their original boxing/ownership operations.
Pinned lean.h2044/2164 specifies both casts; no signed reinterpretation or
out-of-range truncation is accepted at external input.

Validation: the retained384MiB REPL passed15 tests/679 assertions independently
in both recursive and explicit drivers. The focused suite includes genuine
original constructors/owned wrappers, all semantic domains, static storage/cache
models, raw-borrow/preclaim guards, code/host/fork boundaries,4096-node application
spines, shared DAGs, named cycle/work/interrupt rejection and scalar casts.
All256 byte inputs pass raw/boxed widening; high64-bit narrowing and invalid
external lanes are covered. The source fixture's74 rows/23 extern declarations
were statically checked against the exact registered ABI tuples. Independent
native evidence contains54 regular source cases passing both official `--run`
and generated-C/native modes. These are separate evidence sets; model adversaries
are not claimed to be native-produced well-typed ASTs.

Java source SHA256:
`d84d02aa1a38f976de8060c19f21eadfdd8e0a4f8fd038ff4ff4bbed12a048d6`.
Tested jar SHA256:
`948113fd944bb108ed683fffe2d0e7cf8cc26b883d5350bb318019c612317b52`.
The agent ran bounded Java11 compilation, static source/delimiter/diff checks and
the offline native-evidence verifier. Root ran the Clojure suites in the existing
retained JVM; no new Clojure/test JVM or full image/Init replay was launched.
Independent pinned-source review found no remaining valid-source comparator
blocker. The combined integration/full regression gate remains root-owned.
