# Pinned layout and scalar runtime unit

This unit adds six exact native ABI bindings, with IDs 531–536: the four original
IR Checker layout queries, UInt32.decLt, and UInt64.toNat. It adds no execution
lane, Node field, action, policy, importer behavior or callback. UInt16 remains
unsupported. The original owning boxed wrappers execute as ordinary guest IR.

The layout queries return the pinned 64-bit target's 256/1024/243/8 limits.
Canonical Unit Long zero is checked before raw entry and saturated AP claims in
both drivers, and at primitive execution for guest FAP. An arbitrary owned Node
cannot be consumed as Unit. Source wrappers can already have executed guest
instructions before a downstream failure; there is no whole-wrapper rollback.

UInt32 parameters use existing canonical zero-extended long slots, so ordinary
long less-than is unsigned-correct over their validated domain. UInt64-to-Nat
uses the existing unsigned external scalar conversion and the object result
lane: low values return Long, high-bit values exact nonnegative BigInteger.
The public scalar boundary rejects negative and out-of-range inputs. Genuine
boxed UInt64 uses an owned eight-byte scalar Node and its original unbox/release
instructions, not generic object-number coercion.

All six high-numbered operations are in the explicit scalar-membership switch,
so recursive/external and explicit/slot dispatch use the same implementation.
No per-engine state is added; existing scalar pause and fork transport suffices.

The fixture contains sixteen exact original CAS rows; twelve execute and the
remaining four document future UInt16 work. Its provenance pins the accepted
index and Lean commit, lean.h and Checker.lean hashes, fixture hash, and upstream
license. Source anchors are lean.h:92,106–107,1504,2113,3296–3310 and
Lean/Compiler/IR/Checker.lean:14–29. Absolute paths are confined to ignored local
receipts and are not needed by the tracked fixture.

The source checkpoint is
`8d24319da076089fcc553f762cfc643eeecf9ca090037102478515e40396513d`;
its immutable Java 11 jar has SHA
`4977283a1bf18c9a5dfba994f5e210de4a9ab1b0f581bbbd4c3c6c74f9ab62f0`.
Independent source review cleared the exact ABI, dispatch, lane conversion and
preclaim Unit guards. The author compiled Java with a bounded 256 MiB javac,
verified original raw CAS hashes/parsed equality and audited the patch. No author
interpreter JVM or native program was launched. Retained-REPL results are recorded
separately when supplied by the parent.

The eight-test matrix separates authentic original wrappers from synthetic
transport callers. Raw/wrapped/AP semantics and boundary validation cover both
drivers. Code/Host pause cases run only in the explicit driver, using modeled
ordinary callers around the original conversion; they exercise existing transport
rather than introducing a new transport implementation. Both Java and this test
source received independent review before execution.

Parent-retained execution passed all eight tests in each driver on that exact
source/jar: recursive 226 assertions, explicit 235, zero failures/errors at
384 MiB. Receipt `target/java-layout-scalar-runtime-v1/focused-v1.out` has SHA
`9520bc578c97fbd8a857ad54699a4b4d0c0ddcb33dacb9ec0de3e9cb2443cd65`. The clean runner adds two count-guarded groups (8/8).
This is focused unit evidence; integration and original frontend progress are
separate parent observations. The optional Lean oracle source is supplied for
bounded parent execution; no native observation is claimed by this commit.
