# Certified local pointer identity

Implemented research profile, 2026-10-30. This permits the original Name
comparison idiom without exposing an escaping raw-address API. It supplies
virtual object identity, not native/JVM addresses, dereferencing, FFI pointers,
native allocation order, address printing, or pointer-cache relocation.

## Exact body admission

The reserved primitive has its original ABI:
`ptrAddrUnsafe / lean_ptr_addr : (erased, @&tobject) -> usize`. Header admission
can describe it, but executable use requires a certificate for an exact direct
FAP Expr in the current immutable PreparedBody. No function-name heuristic,
caller-supplied flag, digest or ambient permission grants this certificate.

Ordinary lexical scope, unique-binder and lane validation runs first. A closed
whole-body scan then collects direct pointer-producing definitions and audits
every operand use, including unreachable joins and case alternatives. Every
pointer definition must have at least one syntactic use. Its only permitted
uses are the two operands of the reserved USize.decEq intrinsic, with both
operands directly pointer-defined in the same function. Repeated equality uses
and comparing a definition with itself are safe. Parameters, literals, cache
loads, host replies and join parameters never become pointer-origin definitions.

Return, box, store, arithmetic, ordinary calls, captures, AP and join transfer
reject pointer operands. Unknown analysis opcodes reject. This retains all
original instructions, dependencies, ABIs and source hashes; it performs no IR
rewrite or substitution. The private immutable certificate identifies actual
Expr objects. Preparation/materialization publishes it transactionally with its
PreparedBody, preserving inherited body/site identity in descendants.

Both drivers pass the actual PreparedBody and Expr to the dedicated typed FAP
helper. Recursive evaluation passes its local descriptor explicitly, so nested
calls and failures have no ambient permission state to restore. Explicit
evaluation uses its saved activePrepared, including after Host/Code suspension,
fork, return and descendant installation. Other intrinsic entry helpers reject
the pointer operation unconditionally. Fuel/instruction accounting stays on the
existing FAP path; no pointer instruction is replayed.

Raw root calls, PAP construction, makeClosure, imported closures, generic AP,
object-argument admission and Host reply admission reject first-class raw pointer
closures. The original boxed raw-address wrapper fails preparation because its
address escapes through boxing. A trusted HostExtern cannot override the
reserved symbol. Neither a certified caller nor a scalar-returning raw closure
can bypass these independent fences.

## Runtime representation and ownership

The first operand domain is live Nodes and canonical nonnegative Java Long
immediates. Long n observes tagged bits `(n << 1) | 1`; zero observes 1 and
Long.MAX_VALUE observes all-one bits. Strings, BigInteger (including zero),
negative Long and arbitrary host objects reject. This is a runtime representation
contract, not proof of arbitrary source-type origin: GraphInt normalization can
erase distinctions between native immediate Nat and native heap Int. The
reached Name representation uses actual Name Nodes or anonymous Long zero.
Broader Int/String/large-Nat identity needs a separate authenticated carrier policy.

A live Node receives a lazily allocated nonzero, eight-aligned word. Repeated
observation preserves it across tag changes and ordinary mutation of that same
allocation. Replacing an allocation produces a fresh identity when observed.
Dead Nodes reject. Logical RC, isShared and guest ownership are unchanged;
observation creates no guest credit or field mutation.

PointerMetadata wraps existing kind metadata using only a long word, an opaque
branch-owner token and inner NodeMetadata. It adds no common Node field. Array and ByteArray
size/state and closure Generation accessors unwrap it centrally; writes to
kind state preserve the wrapper. Metadata owns no guest values, Interpreter,
source lease or callback. The owner token is a plain Object, not the engine.

A shared atomic monotone allocator retains only its next scalar word and never
reuses observed identities. It serves independent engines/forks in this isolated
engine artifact. Exhaustion after the last aligned unsigned word rejects instead
of wrapping to zero. There is no strong Node registry, weak map or free list.
The engine remains thread-confined; concurrent access to one shared mutable Node
is outside its ownership contract.

Node operations and host ingress reject a stamped Node owned by another branch.
An unstamped Node has no previous branch evidence; its first observation claims
it under the existing trusted complete-owner contract. This does not implement
general graph ownership inference or a sandbox against reflective host mutation.

## Fork and authority limits

One existing fork memo copies all aliases, frames, roots and requests. An
observed Node keeps its word but gets the child's owner token; inner mutable
ArrayState and ByteArrayState copy while immutable Generation shares. Foreign ownership is checked
before copying, so fork cannot relabel a foreign stamped Node. Nodes cloned
before observation may acquire distinct fresh words in different siblings.
New sibling allocations share the allocator and cannot accidentally collide.

The certificate forbids introducing fresh identities into imported numerical
pointer caches, external address words, hashing, ordering or arithmetic. Thus
this identity-only gate needs no numerical-cache relocation. It does not prove
unrelated imported numerical state valid. Any broader pointer feature requires
its own provenance and cache-lifetime contract; no raw word becomes a capability.

## Bounded evidence

The exact pinned 12-row Name.quickCmpImpl closure and genuine Name constructor/
hash fixture run unchanged. Alias Names return equality; distinct equal Names
use actual hash/structural fallback; unequal Names compare normally. The numeric
private Name component remains numeric. No native address ordering is involved.

Sixteen focused tests / 127 assertions pass in each execution driver; suspension cases explicitly
use the explicit driver. They exercise mid-observation fork, Code then Host
suspension, descendant installation, independent sibling words, foreign reply
preclaim rejection, array/closure metadata preservation, nested and self-tail
calls, exact-site immutability, allocator exhaustion, forbidden escapes and
raw-address closure admission. An integration test observes a ByteArray, forks
its aliases and writes different bytes into the same spare slot in both branches.
Negative reflective fixtures test the fences;
reflection is not a supported guest authority mechanism.

The combined isolated jar gate passes 552 test executions / 17,314 assertions
across 63 suites at 384 MiB. No full Init/frontend image was restored. The
source-derived 43-global companion (82,272 Nodes, including 90 ByteArrays)
imports and forks with matching census in the retained 384 MiB REPL. With this
runtime, the original header probe advances to 95 original bodies / 4,598 IR
instructions, then stops at the unsupported Lean.Name.beq extern. This is not
complete parser/elaborator/file execution or self-hosting acceptance. Independent
review found no functional blocker and corrected an outdated fixture README.
A paired ordinary-execution RBMap control (seven alternating-order warmed
batches of 100 in each driver) allocates exactly 1,515,859.52 bytes per run both
before and after this feature. No pointer observation occurs in that workload;
this checks that optional identity metadata adds no allocation to ordinary Nodes.
Shared-machine CPU timings vary and do not establish a speedup.
Source hashes, pinned references and Apache2 attribution are in
`test/fixtures/java-pointer-runtime/`.
